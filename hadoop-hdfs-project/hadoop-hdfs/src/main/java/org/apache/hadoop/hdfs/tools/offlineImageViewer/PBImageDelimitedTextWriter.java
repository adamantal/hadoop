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
import org.apache.hadoop.fs.Path;
import org.apache.hadoop.fs.permission.PermissionStatus;
import org.apache.hadoop.hdfs.server.namenode.FsImageProto.INodeSection.INode;
import org.apache.hadoop.hdfs.server.namenode.FsImageProto.INodeSection.INodeDirectory;
import org.apache.hadoop.hdfs.server.namenode.FsImageProto.INodeSection.INodeFile;
import org.apache.hadoop.hdfs.server.namenode.FsImageProto.INodeSection.INodeSymlink;

import java.io.IOException;
import java.io.PrintStream;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.List;

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

  @Override
  public String getEntry(String parent, INode inode) {
    StringBuffer buffer = new StringBuffer();
    String inodeName = inode.getName().toStringUtf8();
    Path path = new Path(parent.isEmpty() ? "/" : parent,
      inodeName.isEmpty() ? "/" : inodeName);
    append(buffer, path.toString());
    PermissionStatus p = null;
    boolean isDir = false;
    boolean hasAcl = false;

    switch (inode.getType()) {
    case FILE:
      INodeFile file = inode.getFile();
      p = getPermission(file.getPermission());
      hasAcl = file.hasAcl() && file.getAcl().getEntriesCount() > 0;
      append(buffer, file.getReplication());
      append(buffer, formatDate(file.getModificationTime()));
      append(buffer, formatDate(file.getAccessTime()));
      append(buffer, file.getPreferredBlockSize());
      append(buffer, file.getBlocksCount());
      append(buffer, FSImageLoader.getFileSize(file));
      append(buffer, 0);  // NS_QUOTA
      append(buffer, 0);  // DS_QUOTA
      break;
    case DIRECTORY:
      INodeDirectory dir = inode.getDirectory();
      p = getPermission(dir.getPermission());
      hasAcl = dir.hasAcl() && dir.getAcl().getEntriesCount() > 0;
      append(buffer, 0);  // Replication
      append(buffer, formatDate(dir.getModificationTime()));
      append(buffer, formatDate(0));  // Access time.
      append(buffer, 0);  // Block size.
      append(buffer, 0);  // Num blocks.
      append(buffer, 0);  // Num bytes.
      append(buffer, dir.getNsQuota());
      append(buffer, dir.getDsQuota());
      isDir = true;
      break;
    case SYMLINK:
      INodeSymlink s = inode.getSymlink();
      p = getPermission(s.getPermission());
      append(buffer, 0);  // Replication
      append(buffer, formatDate(s.getModificationTime()));
      append(buffer, formatDate(s.getAccessTime()));
      append(buffer, 0);  // Block size.
      append(buffer, 0);  // Num blocks.
      append(buffer, 0);  // Num bytes.
      append(buffer, 0);  // NS_QUOTA
      append(buffer, 0);  // DS_QUOTA
      break;
    default:
      break;
    }
    assert p != null;
    String dirString = isDir ? "d" : "-";
    String aclString = hasAcl ? "+" : "";
    append(buffer, dirString + p.getPermission().toString() + aclString);
    append(buffer, p.getUserName());
    append(buffer, p.getGroupName());
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
    final String snapshotFolderName = "/.snapshot/";
    List<INode> snapshotRoots = getSnapshotRoots();
    for (INode snapshotRoot : snapshotRoots) {
      StringBuffer buffer = new StringBuffer();
      long parentId = snapshotRoot.getId();
      String parentPath = getParentPath(parentId);
      parentPath += getNodeName(parentId);
      parentPath += snapshotFolderName;
      Path path = new Path(parentPath, snapshotRoot.getName().toStringUtf8());
      append(buffer, path.toString());
      if (snapshotRoot.getType() != INode.Type.DIRECTORY) {
        throw new IOException("Snapshot root is not directory!");
      }
      INodeDirectory dir = snapshotRoot.getDirectory();
      PermissionStatus p = getPermission(dir.getPermission());
      boolean hasAcl = dir.hasAcl() && dir.getAcl().getEntriesCount() > 0;
      append(buffer, 0);  // Replication
      append(buffer, formatDate(dir.getModificationTime()));
      append(buffer, formatDate(0));  // Access time.
      append(buffer, 0);  // Block size.
      append(buffer, 0);  // Num blocks.
      append(buffer, 0);  // Num bytes.
      append(buffer, dir.getNsQuota());
      append(buffer, dir.getDsQuota());
      String aclString = hasAcl ? "+" : "";
      append(buffer, "d" + p.getPermission().toString() + aclString);
      append(buffer, p.getUserName());
      append(buffer, p.getGroupName());

      printIfNotEmpty(buffer.substring(1));
    }
  }
}
