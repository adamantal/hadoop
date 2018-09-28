/**
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.hadoop.hdfs.tools.offlineImageViewer;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import org.apache.commons.io.FileUtils;
import org.apache.hadoop.conf.Configuration;
import org.apache.hadoop.fs.Path;
import org.apache.hadoop.fs.permission.PermissionStatus;
import org.apache.hadoop.hdfs.server.namenode.FSImageFormatPBINode;
import org.apache.hadoop.hdfs.server.namenode.FSImageFormatProtobuf;
import org.apache.hadoop.hdfs.server.namenode.FSImageFormatProtobuf.SectionName;
import org.apache.hadoop.hdfs.server.namenode.FSImageUtil;
import org.apache.hadoop.hdfs.server.namenode.FsImageProto;
import org.apache.hadoop.hdfs.server.namenode.FsImageProto.FileSummary;
import org.apache.hadoop.hdfs.server.namenode.FsImageProto.INodeSection;
import org.apache.hadoop.hdfs.server.namenode.FsImageProto.INodeSection.INode;
import org.apache.hadoop.hdfs.server.namenode.INodeId;
import org.apache.hadoop.io.IOUtils;
import org.apache.hadoop.util.LimitInputStream;
import org.apache.hadoop.util.Time;
import org.fusesource.leveldbjni.JniDBFactory;
import org.iq80.leveldb.DB;
import org.iq80.leveldb.Options;
import org.iq80.leveldb.WriteBatch;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.BufferedInputStream;
import java.io.Closeable;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.io.RandomAccessFile;
import java.io.UnsupportedEncodingException;
import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * This class reads the protobuf-based fsimage and generates text output
 * for each inode to {@link PBImageTextWriter#out}. The sub-class can override
 * {@link getEntry()} to generate formatted string for each inode.
 *
 * Since protobuf-based fsimage does not guarantee the order of inodes and
 * directories, PBImageTextWriter runs two-phase scans:
 *
 * <ol>
 *   <li>The first phase, PBImageTextWriter scans the INode sections to reads the
 *   filename of each directory. It also scans the INode_Dir sections to loads
 *   the relationships between a directory and its children. It uses these metadata
 *   to build FS namespace and stored in {@link MetadataMap}</li>
 *   <li>The second phase, PBImageTextWriter re-scans the INode sections. For each
 *   inode, it looks up the path of the parent directory in the {@link MetadataMap},
 *   and generate output.</li>
 * </ol>
 *
 * Two various of {@link MetadataMap} are provided. {@link InMemoryMetadataDB}
 * stores all metadata in memory (O(n) memory) while
 * {@link LevelDBMetadataMap} stores metadata in LevelDB on disk (O(1) memory).
 * User can choose between them based on the time/space tradeoffs.
 */
abstract class PBImageTextWriter implements Closeable {
  private static final Logger LOG =
      LoggerFactory.getLogger(PBImageTextWriter.class);

  /**
   * This metadata map is used to construct the namespace before generating
   * text outputs.
   *
   * It contains two mapping relationships:
   * <p>
   *   <li>It maps each inode (inode Id) to its parent directory (inode Id).</li>
   *   <li>It maps each directory from its inode Id.</li>
   * </p>
   */
  private static interface MetadataMap extends Closeable {
    /**
     * Associate an inode with its parent directory.
     */
    public void putDirChild(long parentId, long childId) throws IOException;

    /**
     * Associate a directory with its inode Id.
     */
    public void putDir(INode dir) throws IOException;

    /** Get the full path of the parent directory for the given inode. */
    public String getParentPath(long inode) throws IOException;

    /** Synchronize metadata to persistent storage, if possible */
    public void sync() throws IOException;

    /** Returns the name of inode. */
    String getName(long id) throws IOException;
  }

  /**
   * Maintain all the metadata in memory.
   */
  private static class InMemoryMetadataDB implements MetadataMap {
    /**
     * Represent a directory in memory.
     */
    private static class Dir {
      private final long inode;
      private Dir parent = null;
      private String name;
      private String cachedPath = null;

      Dir(long inode, String name) {
        this.inode = inode;
        this.name = name;
      }

      private long getId() {
        return inode;
      }

      private void setParent(Dir parent) {
        Preconditions.checkState(this.parent == null);
        this.parent = parent;
      }

      /**
       * Returns the full path of this directory.
       */
      private String getPath(boolean useCache) {
        if (this.parent == null) {
          return "/";
        }
        if (!useCache || this.cachedPath == null) {
          this.cachedPath = new Path(parent.getPath(useCache), name.isEmpty() ? "/" : name).
              toString();
        }
        return this.cachedPath;
      }

      String getName() {
        return name;
      }

      void setName(String name) {
        this.name = name;
      }

      @Override
      public boolean equals(Object o) {
        return o instanceof Dir && inode == ((Dir) o).inode;
      }

      @Override
      public int hashCode() {
        return Long.valueOf(inode).hashCode();
      }
    }

    /** INode Id to Dir object mapping */
    private Map<Long, Dir> dirMap = new HashMap<>();

    /** Children to parent directory INode ID mapping. */
    private Map<Long, Dir> dirChildMap = new HashMap<>();

    InMemoryMetadataDB() {
    }

    @Override
    public void close() throws IOException {
    }

    @Override
    public void putDirChild(long parentId, long childId) {
      Dir parent = dirMap.get(parentId);
      Dir child = dirMap.get(childId);
      if (child != null) {
        child.setParent(parent);
      }
      Preconditions.checkState(!dirChildMap.containsKey(childId));
      dirChildMap.put(childId, parent);
    }

    @Override
    public void putDir(INode p) {
      Preconditions.checkState(!dirMap.containsKey(p.getId()));
      Dir dir = new Dir(p.getId(), p.getName().toStringUtf8());
      dirMap.put(p.getId(), dir);
    }

    @Override
    public String getParentPath(long inode) throws IOException {
      if (inode == INodeId.ROOT_INODE_ID) {
        return "";
      }
      Dir parent = dirChildMap.get(inode);
      if (parent == null) {
        // The inode is an INodeReference, which is generated from snapshot.
        // For delimited oiv tool, no need to print out metadata in snapshots.
        PBImageTextWriter.ignoreSnapshotName(inode);
      }
      return parent.getPath(true);
    }

    @Override
    public void sync() {
    }

    @Override
    public String getName(long id) throws IOException {
      Dir dir = dirMap.get(id);
      if (dir != null) {
        return dir.getName();
      }
      PBImageTextWriter.ignoreSnapshotName(id);
      return null;
    }

    public void setName(long id, String name) throws IOException {
      Dir dir = dirMap.get(id);
      if (dir != null) {
        dir.setName(name);
      }
      PBImageTextWriter.ignoreSnapshotName(id);
    }

    /*public boolean isInShapshot(long id, Set<Long> snapshotRoots) {
      if (snapshotRoots.contains(id)) {
        return true;
      }
      Dir parent;
      while ((parent = dirChildMap.get(id)) != null) {
        if (snapshotRoots.contains(parent.getId())) {
          return true;
        }
      }
      return false;
    }*/
  }

  /**
   * A MetadataMap that stores metadata in LevelDB.
   */
  private static class LevelDBMetadataMap implements MetadataMap {
    /**
     * Store metadata in LevelDB.
     */
    private static class LevelDBStore implements Closeable {
      private DB db = null;
      private WriteBatch batch = null;
      private int writeCount = 0;
      private static final int BATCH_SIZE = 1024;

      LevelDBStore(final File dbPath) throws IOException {
        Options options = new Options();
        options.createIfMissing(true);
        options.errorIfExists(true);
        db = JniDBFactory.factory.open(dbPath, options);
        batch = db.createWriteBatch();
      }

      @Override
      public void close() throws IOException {
        if (batch != null) {
          IOUtils.cleanup(null, batch);
          batch = null;
        }
        IOUtils.cleanup(null, db);
        db = null;
      }

      public void put(byte[] key, byte[] value) throws IOException {
        batch.put(key, value);
        writeCount++;
        if (writeCount >= BATCH_SIZE) {
          sync();
        }
      }

      public byte[] get(byte[] key) throws IOException {
        return db.get(key);
      }

      public void sync() throws IOException {
        try {
          db.write(batch);
        } finally {
          batch.close();
          batch = null;
        }
        batch = db.createWriteBatch();
        writeCount = 0;
      }
    }

    /**
     * A LRU cache for directory path strings.
     *
     * The key of this LRU cache is the inode of a directory.
     */
    private static class DirPathCache extends LinkedHashMap<Long, String> {
      private final static int CAPACITY = 16 * 1024;

      DirPathCache() {
        super(CAPACITY);
      }

      @Override
      protected boolean removeEldestEntry(Map.Entry<Long, String> entry) {
        return super.size() > CAPACITY;
      }
    }

    /** Map the child inode to the parent directory inode. */
    private LevelDBStore dirChildMap = null;
    /** Directory entry map */
    private LevelDBStore dirMap = null;
    private DirPathCache dirPathCache = new DirPathCache();

    LevelDBMetadataMap(String baseDir) throws IOException {
      File dbDir = new File(baseDir);
      if (dbDir.exists()) {
        FileUtils.deleteDirectory(dbDir);
      }
      if (!dbDir.mkdirs()) {
        throw new IOException("Failed to mkdir on " + dbDir);
      }
      try {
        dirChildMap = new LevelDBStore(new File(dbDir, "dirChildMap"));
        dirMap = new LevelDBStore(new File(dbDir, "dirMap"));
      } catch (IOException e) {
        LOG.error("Failed to open LevelDBs", e);
        IOUtils.cleanup(null, this);
      }
    }

    @Override
    public void close() throws IOException {
      IOUtils.cleanup(null, dirChildMap, dirMap);
      dirChildMap = null;
      dirMap = null;
    }

    private static byte[] toBytes(long value) {
      return ByteBuffer.allocate(8).putLong(value).array();
    }

    private static byte[] toBytes(String value)
        throws UnsupportedEncodingException {
      return value.getBytes("UTF-8");
    }

    private static long toLong(byte[] bytes) {
      Preconditions.checkArgument(bytes.length == 8);
      return ByteBuffer.wrap(bytes).getLong();
    }

    private static String toString(byte[] bytes) throws IOException {
      try {
        return new String(bytes, "UTF-8");
      } catch (UnsupportedEncodingException e) {
        throw new IOException(e);
      }
    }

    @Override
    public void putDirChild(long parentId, long childId) throws IOException {
      dirChildMap.put(toBytes(childId), toBytes(parentId));
    }

    @Override
    public void putDir(INode dir) throws IOException {
      Preconditions.checkArgument(dir.hasDirectory(),
          "INode %s (%s) is not a directory.", dir.getId(), dir.getName());
      dirMap.put(toBytes(dir.getId()), toBytes(dir.getName().toStringUtf8()));
    }

    @Override
    public String getParentPath(long inode) throws IOException {
      if (inode == INodeId.ROOT_INODE_ID) {
        return "/";
      }
      byte[] bytes = dirChildMap.get(toBytes(inode));
      if (bytes == null) {
        // The inode is an INodeReference, which is generated from snapshot.
        // For delimited oiv tool, no need to print out metadata in snapshots.
        PBImageTextWriter.ignoreSnapshotName(inode);
      }
      if (bytes.length != 8) {
        throw new IOException(
            "bytes array length error. Actual length is " + bytes.length);
      }
      long parent = toLong(bytes);
      if (!dirPathCache.containsKey(parent)) {
        bytes = dirMap.get(toBytes(parent));
        if (parent != INodeId.ROOT_INODE_ID && bytes == null) {
          // The parent is an INodeReference, which is generated from snapshot.
          // For delimited oiv tool, no need to print out metadata in snapshots.
          PBImageTextWriter.ignoreSnapshotName(parent);
        }
        String parentName = toString(bytes);
        String parentPath =
            new Path(getParentPath(parent),
                parentName.isEmpty()? "/" : parentName).toString();
        dirPathCache.put(parent, parentPath);
      }
      return dirPathCache.get(parent);
    }

    @Override
    public void sync() throws IOException {
      dirChildMap.sync();
      dirMap.sync();
    }

    @Override
    public String getName(long id) throws IOException {
      byte[] bytes = dirMap.get(toBytes(id));
      if (bytes != null) {
        return toString(bytes);
      }
      PBImageTextWriter.ignoreSnapshotName(id);
      return null;
    }
  }

  private ImmutableList<Long> refIdList = null;
  private String[] stringTable;
  private PrintStream out;
  private MetadataMap metadataMap = null;
  private boolean addSnapshots;
  private ArrayList<FsImageProto.SnapshotSection.Snapshot> snapshots = new ArrayList<>();

  /**
   * Construct a PB FsImage writer to generate text file.
   * @param out the writer to output text information of fsimage.
   * @param tempPath the path to store metadata. If it is empty, store metadata
   *                 in memory instead.
   */
  PBImageTextWriter(PrintStream out, String tempPath, boolean addSnapshots)
      throws IOException {
    this.out = out;
    this.addSnapshots = addSnapshots;
    if (tempPath.isEmpty()) {
      metadataMap = new InMemoryMetadataDB();
    } else {
      metadataMap = new LevelDBMetadataMap(tempPath);
    }
  }

  @Override
  public void close() throws IOException {
    out.flush();
    IOUtils.cleanup(null, metadataMap);
  }

  List<FsImageProto.SnapshotSection.Snapshot> getSnapshots() {
    return snapshots;
  }

  /**
   * Get text output for the given inode.
   * @param parent the path of parent directory
   * @param inode the INode object to output.
   */
  abstract protected String getEntry(String parent, INode inode);

  /**
   * Get text output for the header line.
   */
  abstract protected String getHeader();

  /**
   * After the processor has iterated through the inodes from
   * INodeDirectorySection, we can output extra information.
   *
   * @throws IOException
   */
  abstract protected void afterOutput() throws IOException;

  /**
   * For inodes not mentioned in the INodeDirectorySection (e.g. from
   * snapshot) we can query their parent's path through this function.
   *
   * @param id
   * @return the path of the parent's inode
   * @throws IOException
   */
  String getParentPath(long id) throws IOException {
    return metadataMap.getParentPath(id);
  }

  boolean isAddSnapshots() {
    return addSnapshots;
  }

  public void visit(RandomAccessFile file) throws IOException {
    Configuration conf = new Configuration();
    if (!FSImageUtil.checkFileFormat(file)) {
      throw new IOException("Unrecognized FSImage");
    }

    FileSummary summary = FSImageUtil.loadSummary(file);

    try (FileInputStream fin = new FileInputStream(file.getFD())) {
      InputStream is;
      ArrayList<FileSummary.Section> sections =
          Lists.newArrayList(summary.getSectionsList());
      Collections.sort(sections,
          new Comparator<FileSummary.Section>() {
            @Override
            public int compare(FsImageProto.FileSummary.Section s1,
                FsImageProto.FileSummary.Section s2) {
              FSImageFormatProtobuf.SectionName n1 =
                  FSImageFormatProtobuf.SectionName.fromString(s1.getName());
              FSImageFormatProtobuf.SectionName n2 =
                  FSImageFormatProtobuf.SectionName.fromString(s2.getName());
              if (n1 == null) {
                return n2 == null ? 0 : -1;
              } else if (n2 == null) {
                return -1;
              } else {
                return n1.ordinal() - n2.ordinal();
              }
            }
          });

      for (FileSummary.Section section : sections) {
        fin.getChannel().position(section.getOffset());
        is = FSImageUtil.wrapInputStreamForCompression(conf,
            summary.getCodec(), new BufferedInputStream(new LimitInputStream(
                fin, section.getLength())));
        switch (SectionName.fromString(section.getName())) {
        case STRING_TABLE:
          LOG.info("Loading string table");
          stringTable = FSImageLoader.loadStringTable(is);
          break;
        case INODE_REFERENCE:
          // Load INodeReference so that all INodes can be processed.
          LOG.info("Loading inode references");
          refIdList = FSImageLoader.loadINodeReferenceSection(is);
          break;
        default:
          break;
        }
      }

      loadDirectories(fin, sections, summary, conf);
      loadINodeDirSection(fin, sections, summary, conf);
      if (addSnapshots) {
        loadSnapshotSection(fin, sections, summary, conf);
      }
      metadataMap.sync();
      output(conf, summary, fin, sections);
      afterOutput();
    }
  }

  String getNodeName(long id) throws IOException {
    return metadataMap.getName(id);
  }

  private void output(Configuration conf, FileSummary summary,
      FileInputStream fin, ArrayList<FileSummary.Section> sections)
      throws IOException {
    InputStream is;
    long startTime = Time.monotonicNow();
    out.println(getHeader());
    for (FileSummary.Section section : sections) {
      if (SectionName.fromString(section.getName()) == SectionName.INODE) {
        fin.getChannel().position(section.getOffset());
        is = FSImageUtil.wrapInputStreamForCompression(conf,
            summary.getCodec(), new BufferedInputStream(new LimitInputStream(
                fin, section.getLength())));
        outputINodes(is);
      }
    }
    long timeTaken = Time.monotonicNow() - startTime;
    LOG.debug("Time to output inodes: {}ms", timeTaken);
  }

  protected PermissionStatus getPermission(long perm) {
    return FSImageFormatPBINode.Loader.loadPermission(perm, stringTable);
  }

  /** Load the directories in the INode section. */
  private void loadDirectories(
      FileInputStream fin, List<FileSummary.Section> sections,
      FileSummary summary, Configuration conf)
      throws IOException {
    LOG.info("Loading directories");
    long startTime = Time.monotonicNow();
    for (FileSummary.Section section : sections) {
      if (SectionName.fromString(section.getName())
          == SectionName.INODE) {
        fin.getChannel().position(section.getOffset());
        InputStream is = FSImageUtil.wrapInputStreamForCompression(conf,
            summary.getCodec(), new BufferedInputStream(new LimitInputStream(
                fin, section.getLength())));
        loadDirectoriesInINodeSection(is);
      }
    }
    long timeTaken = Time.monotonicNow() - startTime;
    LOG.info("Finished loading directories in {}ms", timeTaken);
  }

  private void loadINodeDirSection(
      FileInputStream fin, List<FileSummary.Section> sections,
      FileSummary summary, Configuration conf)
      throws IOException {
    LOG.info("Loading INode directory section.");
    long startTime = Time.monotonicNow();
    for (FileSummary.Section section : sections) {
      if (SectionName.fromString(section.getName())
          == SectionName.INODE_DIR) {
        fin.getChannel().position(section.getOffset());
        InputStream is = FSImageUtil.wrapInputStreamForCompression(conf,
            summary.getCodec(), new BufferedInputStream(
                new LimitInputStream(fin, section.getLength())));
        buildNamespace(is);
      }
    }
    long timeTaken = Time.monotonicNow() - startTime;
    LOG.info("Finished loading INode directory section in {}ms", timeTaken);
  }

  private void loadSnapshotSection(FileInputStream fin,
      List<FileSummary.Section> sections, FileSummary summary,
      Configuration conf) throws IOException {
    LOG.info("Loading SnapshotSection.");
    long startTime = Time.monotonicNow();
    for (FileSummary.Section section : sections) {
      if (SectionName.fromString(section.getName())
          == SectionName.SNAPSHOT) {
        fin.getChannel().position(section.getOffset());
        InputStream is = FSImageUtil.wrapInputStreamForCompression(conf,
            summary.getCodec(), new BufferedInputStream(
                new LimitInputStream(fin, section.getLength())));
        saveSnapshotRoots(is);
      }
    }
    long timeTaken = Time.monotonicNow() - startTime;
    LOG.info("Finished loading SnapshotSection in {}ms", timeTaken);
  }

  /**
   * Load the filenames of the directories from the INode section.
   */
  private void loadDirectoriesInINodeSection(InputStream in) throws IOException {
    INodeSection s = INodeSection.parseDelimitedFrom(in);
    LOG.info("Loading directories in INode section.");
    int numDirs = 0;
    for (int i = 0; i < s.getNumInodes(); ++i) {
      INode p = INode.parseDelimitedFrom(in);
      if (LOG.isDebugEnabled() && i % 10000 == 0) {
        LOG.debug("Scanned {} inodes.", i);
      }
      if (p.hasDirectory()) {
        metadataMap.putDir(p);
        numDirs++;
      }
    }
    LOG.info("Found {} directories in INode section.", numDirs);
  }

  private void saveSnapshotRoots(InputStream is) throws IOException {
    FsImageProto.SnapshotSection s =
        FsImageProto.SnapshotSection.parseDelimitedFrom(is);
    for (int i = 0; i < s.getNumSnapshots(); ++i) {
      FsImageProto.SnapshotSection.Snapshot snapshot =
          FsImageProto.SnapshotSection.Snapshot.parseDelimitedFrom(is);
      snapshots.add(snapshot);
    }
  }

  /**
   * Scan the INodeDirectory section to construct the namespace.
   */
  private void buildNamespace(InputStream in)
      throws IOException {
    int count = 0;
    while (true) {
      FsImageProto.INodeDirectorySection.DirEntry e =
          FsImageProto.INodeDirectorySection.DirEntry.parseDelimitedFrom(in);
      if (e == null) {
        break;
      }
      count++;
      if (LOG.isDebugEnabled() && count % 10000 == 0) {
        LOG.debug("Scanned {} directories.", count);
      }
      long parentId = e.getParent();
      for (int i = 0; i < e.getChildrenCount(); i++) {
        long childId = e.getChildren(i);
        metadataMap.putDirChild(parentId, childId);
      }
      for (int i = e.getChildrenCount();
           i < e.getChildrenCount() + e.getRefChildrenCount(); i++) {
        int refId = e.getRefChildren(i - e.getChildrenCount());
        metadataMap.putDirChild(parentId, refIdList.get(refId));
      }
    }
    LOG.info("Scanned {} INode directories to build namespace.", count);
  }

  void printIfNotEmpty(String line) {
    if (!line.isEmpty()) {
      out.println(line);
    }
  }

  private void outputINodes(InputStream in) throws IOException {
    INodeSection s = INodeSection.parseDelimitedFrom(in);
    LOG.info("Found {} INodes in the INode section", s.getNumInodes());
    long ignored = 0;
    long ignoredSnapshots = 0;
    for (int i = 0; i < s.getNumInodes(); ++i) {
      INode p = INode.parseDelimitedFrom(in);
      try {
        String parentPath = metadataMap.getParentPath(p.getId());
        printIfNotEmpty(getEntry(parentPath, p));
      } catch (IOException ioe) {
        ignored++;
        if (!(ioe instanceof IgnoreSnapshotException)) {
          LOG.warn("Exception caught, ignoring node:{}", p.getId(), ioe);
        } else {
          ignoredSnapshots++;
          if (LOG.isDebugEnabled()) {
            LOG.debug("Exception caught, ignoring node:{}.", p.getId(), ioe);
          }
        }
      }

      if (LOG.isDebugEnabled() && i % 100000 == 0) {
        LOG.debug("Outputted {} INodes.", i);
      }
    }
    if (ignored > 0) {
      LOG.warn("Ignored {} nodes, including {} in snapshots. Please turn on"
              + " debug log for details", ignored, ignoredSnapshots);
    }
    LOG.info("Outputted {} INodes.", s.getNumInodes());
  }

  static void ignoreSnapshotName(long inode) throws IOException {
    // Ignore snapshots - we want the output similar to -ls -R.
    if (LOG.isDebugEnabled()) {
      LOG.debug("No snapshot name found for inode {}", inode);
    }
    throw new IgnoreSnapshotException();
  }
}
