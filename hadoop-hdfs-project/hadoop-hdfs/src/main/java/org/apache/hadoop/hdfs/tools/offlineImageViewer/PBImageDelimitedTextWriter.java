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

import org.apache.commons.lang3.StringUtils;
import org.apache.commons.text.StringEscapeUtils;
import org.apache.hadoop.conf.Configuration;
import org.apache.hadoop.fs.Path;
import org.apache.hadoop.fs.permission.PermissionStatus;
import org.apache.hadoop.hdfs.server.namenode.FSImageFormatProtobuf;
import org.apache.hadoop.hdfs.server.namenode.FSImageUtil;
import org.apache.hadoop.hdfs.server.namenode.FsImageProto;
import org.apache.hadoop.hdfs.server.namenode.FsImageProto.INodeSection.INode;
import org.apache.hadoop.hdfs.server.namenode.FsImageProto.INodeSection.INodeDirectory;
import org.apache.hadoop.hdfs.server.namenode.FsImageProto.INodeSection.INodeFile;
import org.apache.hadoop.hdfs.server.namenode.FsImageProto.INodeSection.INodeSymlink;
import org.apache.hadoop.hdfs.server.namenode.FsImageProto.SnapshotDiffSection;
import org.apache.hadoop.hdfs.server.namenode.FsImageProto.SnapshotDiffSection.DiffEntry;
import org.apache.hadoop.util.LimitInputStream;
import org.apache.hadoop.util.Time;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.BufferedInputStream;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * A PBImageDelimitedTextWriter generates a text representation of the PB fsimage,
 * with each element separated by a delimiter string.  All of the elements
 * common to both inodes and inodes-under-construction are included. When
 * processing an fsimage with a layout version that did not include an
 * element, such as AccessTime, the output file will include a column
 * for the value, but no value will be included.
 *
 * Individual block information for each file is not currently included.
 *
 * The default delimiter is tab, as this is an unlikely value to be included in
 * an inode path or other text metadata. The delimiter value can be via the
 * constructor.
 */
public class PBImageDelimitedTextWriter extends PBImageTextWriter {
  private static final Logger LOG =
      LoggerFactory.getLogger(PBImageDelimitedTextWriter.class);
  static final String DEFAULT_DELIMITER = "\t";
  private static final String DATE_FORMAT="yyyy-MM-dd HH:mm";
  private final SimpleDateFormat dateFormatter =
      new SimpleDateFormat(DATE_FORMAT);

  private final String delimiter;

  PBImageDelimitedTextWriter(PrintStream out, String delimiter,
      String tempPath, boolean addSnapshots) throws IOException {
    super(out, tempPath, addSnapshots);
    this.delimiter = delimiter;
  }

  private String formatDate(long date) {
    return dateFormatter.format(new Date(date));
  }

  private void append(StringBuffer buffer, int field) {
    buffer.append(delimiter);
    buffer.append(field);
  }

  private void append(StringBuffer buffer, long field) {
    buffer.append(delimiter);
    buffer.append(field);
  }

  static final String CRLF = StringUtils.CR + StringUtils.LF;

  private void append(StringBuffer buffer, String field) {
    buffer.append(delimiter);

    String escapedField = StringEscapeUtils.escapeCsv(field);
    if (escapedField.contains(CRLF)) {
      escapedField = escapedField.replace(CRLF, "%x0D%x0A");
    } else if (escapedField.contains(StringUtils.LF)) {
      escapedField = escapedField.replace(StringUtils.LF, "%x0A");
    }

    buffer.append(escapedField);
  }

  private String getEntry(INodeFile file) {
    StringBuffer buffer = new StringBuffer();
    append(buffer, file.getReplication());
    append(buffer, formatDate(file.getModificationTime()));
    append(buffer, formatDate(file.getAccessTime()));
    append(buffer, file.getPreferredBlockSize());
    append(buffer, file.getBlocksCount());
    append(buffer, FSImageLoader.getFileSize(file));
    append(buffer, 0);  // NS_QUOTA
    append(buffer, 0);  // DS_QUOTA
    PermissionStatus p = getPermission(file.getPermission());
    boolean hasAcl = file.hasAcl() && file.getAcl().getEntriesCount() > 0;
    String aclString = hasAcl ? "+" : "";
    append(buffer, "-" + p.getPermission().toString() + aclString);
    append(buffer, p.getUserName());
    append(buffer, p.getGroupName());
    return buffer.toString();
  }

  private String getEntry(INodeDirectory dir) {
    StringBuffer buffer = new StringBuffer();
    append(buffer, 0);  // Replication
    append(buffer, formatDate(dir.getModificationTime()));
    append(buffer, formatDate(0));  // Access time.
    append(buffer, 0);  // Block size.
    append(buffer, 0);  // Num blocks.
    append(buffer, 0);  // Num bytes.
    append(buffer, dir.getNsQuota());
    append(buffer, dir.getDsQuota());
    PermissionStatus p = getPermission(dir.getPermission());
    boolean hasAcl = dir.hasAcl() && dir.getAcl().getEntriesCount() > 0;
    String aclString = hasAcl ? "+" : "";
    append(buffer, "d" + p.getPermission().toString() + aclString);
    append(buffer, p.getUserName());
    append(buffer, p.getGroupName());
    return buffer.toString();
  }

  private String getEntry(INodeSymlink s) {
    StringBuffer buffer = new StringBuffer();
    append(buffer, 0);  // Replication
    append(buffer, formatDate(s.getModificationTime()));
    append(buffer, formatDate(s.getAccessTime()));
    append(buffer, 0);  // Block size.
    append(buffer, 0);  // Num blocks.
    append(buffer, 0);  // Num bytes.
    append(buffer, 0);  // NS_QUOTA
    append(buffer, 0);  // DS_QUOTA
    PermissionStatus p = getPermission(s.getPermission());
    append(buffer, "-" + p.getPermission().toString());
    append(buffer, p.getUserName());
    append(buffer, p.getGroupName());
    return buffer.toString();
  }

  @Override
  public String getEntry(String parent, INode inode) {
    StringBuffer buffer = new StringBuffer();
    String inodeName = inode.getName().toStringUtf8();
    Path path = new Path(parent.isEmpty() ? "/" : parent,
      inodeName.isEmpty() ? "/" : inodeName);
    append(buffer, path.toString());
    switch (inode.getType()) {
    case FILE:
      append(buffer, getEntry(inode.getFile()));
      break;
    case DIRECTORY:
      append(buffer, getEntry(inode.getDirectory()));
      break;
    case SYMLINK:
      append(buffer, getEntry(inode.getSymlink()));
      break;
    default:
      break;
    }
    return buffer.substring(1);
  }

  @Override
  public String getHeader() {
    StringBuffer buffer = new StringBuffer();
    buffer.append("Path");
    append(buffer, "Replication");
    append(buffer, "ModificationTime");
    append(buffer, "AccessTime");
    append(buffer, "PreferredBlockSize");
    append(buffer, "BlocksCount");
    append(buffer, "FileSize");
    append(buffer, "NSQUOTA");
    append(buffer, "DSQUOTA");
    append(buffer, "Permission");
    append(buffer, "UserName");
    append(buffer, "GroupName");
    return buffer.toString();
  }

  @Override
  public void afterOutput() throws IOException {
    if (isAddSnapshots()) {
      List<FsImageProto.SnapshotSection.Snapshot> snapshots = getSnapshots();
      for (FsImageProto.SnapshotSection.Snapshot snapshot : snapshots) {
        // TODO print out snapshot root (also add to the folder structure?)
        iterateOverSnapshotDiffSection();
        loadRenames();
        for () { // iterate through DiffEntries
          // print inodes using the same logic as before
          // getSnapshotCopy() returns an INodeDirectory
        }
      }
      // Question: what is activeINodes good for?
    }
  }

  private void iterateOverSnapshotDiffSection(FileInputStream fin,
      List<FsImageProto.FileSummary.Section> sections,
      FsImageProto.FileSummary summary, Configuration conf)
      throws IOException {
    LOG.debug("Iterate through SnapshotDiffSection.");
    long startTime = Time.monotonicNow();
    for (FsImageProto.FileSummary.Section section : sections) {
      if (FSImageFormatProtobuf.SectionName.fromString(section.getName())
          == FSImageFormatProtobuf.SectionName.SNAPSHOT_DIFF) {
        fin.getChannel().position(section.getOffset());
        InputStream is = FSImageUtil.wrapInputStreamForCompression(conf,
            summary.getCodec(), new BufferedInputStream(
                new LimitInputStream(fin, section.getLength())));
        getSnapshotDiffs(is, 0);
      }
    }
    long timeTaken = Time.monotonicNow() - startTime;
    LOG.debug("Finished loading SnapshotDiffSection in {}ms", timeTaken);
  }

  private void getSnapshotDiffs(InputStream is, int snapshotId)
      throws IOException {
    SnapshotDiffSection s = SnapshotDiffSection.parseDelimitedFrom(is);
    // hierarchy in the snapshotdiffsection:
    // SnapshotDiffSection -> DiffEntry (can be either
    //      dirDiffEntry or fileDiffEntry)
    // -> FileDiff or DirectoryDiff (-> (multiple) CreatedListEntry))
    while (true) {
      SnapshotDiffSection.DiffEntry diffEntry =
          SnapshotDiffSection.DiffEntry.parseDelimitedFrom(is);
      if (diffEntry == null) {
        break;
      }
      long id = diffEntry.getInodeId();
      // todo do stuff with id
      if (diffEntry.getType() == DiffEntry.Type.DIRECTORYDIFF) {
        for (int i = 0; i < diffEntry.getNumOfDiff(); i++) {
          SnapshotDiffSection.DirectoryDiff dirDiff =
              SnapshotDiffSection.DirectoryDiff.parseDelimitedFrom(is);
          if (dirDiff == null) {
            throw new IOException("Error while loading fsimage: " +
                "DirDiffEntry has missing DirDiffs.");
          }
          if (dirDiff.getSnapshotId() == snapshotId) {
            // todo do stuff with dirDiff
            // todo use activeNodes.remove(deletedInode); if was deleted
            for (int j = 0; j < dirDiff.getCreatedListSize(); j++) {
              SnapshotDiffSection.CreatedListEntry createdListEntry =
                  SnapshotDiffSection.CreatedListEntry.parseDelimitedFrom(is);
              if (createdListEntry == null) {
                throw new IOException("Error while loading fsimage: " +
                    "missing CreatedListEntry.");
              }
              String createdName = createdListEntry.getName().toStringUtf8();
              // todo do stuff with createdName
            }
            break; // can we do this?
          }
        }
      } else if (diffEntry.getType() == DiffEntry.Type.FILEDIFF) {
        for (int i = 0; i < diffEntry.getNumOfDiff(); i++) {
          SnapshotDiffSection.FileDiff fileDiff =
              SnapshotDiffSection.FileDiff.parseDelimitedFrom(is);
          if (fileDiff == null) {
            throw new IOException("Error while loading fsimage: " +
                "FileDiffEntry has missing FileDiffs.");
          }
          if (fileDiff.getSnapshotId() == snapshotId) {
            // todo do stuff with fileDiff
            break; // can we do this?
          }
        }
      }
    }
  }

  private void loadRenames(FileInputStream fin,
      List<FsImageProto.FileSummary.Section> sections,
      FsImageProto.FileSummary summary, Configuration conf)
      throws IOException {
    LOG.debug("Iterate through INodeReferenceSection.");
    long startTime = Time.monotonicNow();
    for (FsImageProto.FileSummary.Section section : sections) {
      if (FSImageFormatProtobuf.SectionName.fromString(section.getName())
          == FSImageFormatProtobuf.SectionName.INODE_REFERENCE) {
        fin.getChannel().position(section.getOffset());
        InputStream is = FSImageUtil.wrapInputStreamForCompression(conf,
            summary.getCodec(), new BufferedInputStream(
                new LimitInputStream(fin, section.getLength())));
        loadRenamesFromINodeRefSection(is, 0);
      }
    }
    long timeTaken = Time.monotonicNow() - startTime;
    LOG.debug("Finished loading SnapshotDiffSection in {}ms", timeTaken);
  }

  private void loadRenamesFromINodeRefSection(InputStream is, int snapshotId)
      throws IOException {
    FsImageProto.INodeReferenceSection s =
        FsImageProto.INodeReferenceSection.parseDelimitedFrom(is);
    while (true) {
      FsImageProto.INodeReferenceSection.INodeReference inodeRef =
          FsImageProto.INodeReferenceSection.INodeReference.parseDelimitedFrom(is);
      if (inodeRef == null) {
        break;
      }
      if (inodeRef.getLastSnapshotId() == snapshotId) {
        String newName = inodeRef.getName().toStringUtf8();
        // do stuff with newName
      }
    }
  }
}
