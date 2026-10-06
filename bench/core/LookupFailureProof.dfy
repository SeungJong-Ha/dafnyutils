include "IOContract.dfy"

module LookupFailureProof {
  import opened BenchWorld
  import C = IOContract

  lemma LookupFailurePositive(
    inodes: map<InodeId, InodeRecord>, tree: InodeTree, segments: seq<string>
  )
    ensures InodeFsLookupTreeSegments(inodes, tree, segments).Err? ==>
              C.IOErrorErrno(InodeFsLookupTreeSegments(inodes, tree, segments).e) > 0
    decreases |segments|
  {
    if tree.id in inodes && |segments| > 0 &&
       inodes[tree.id].node.Directory? && segments[0] in tree.children {
      LookupFailurePositive(inodes, tree.children[segments[0]], segments[1..]);
    }
  }

  lemma DirectFailurePositive(fs: FileSystem, path: Path)
    ensures C.DirectNoFollowResultFields(fs, path).Err? ==>
              C.IOErrorErrno(C.DirectNoFollowResultFields(fs, path).e) > 0
    ensures C.TerminalNoFollowResultFields(fs, path).Err? ==>
              C.IOErrorErrno(C.TerminalNoFollowResultFields(fs, path).e) > 0
  {
    LookupFailurePositive(fs.inodes, fs.namespace, PathSegments(path));
  }

  lemma {:induction false} RawFailurePositive(
    fs: FileSystem, segments: seq<string>, i: nat, current: Path,
    seen: set<Path>, fuel: nat, follow: bool, missing: bool, directory: bool
  )
    requires i <= |segments|
    ensures C.ResolveRawSymlinkSegmentsFields(
              fs, segments, i, current, seen, fuel, follow, missing, directory).Err? ==>
              C.IOErrorErrno(C.ResolveRawSymlinkSegmentsFields(
                               fs, segments, i, current, seen, fuel, follow, missing, directory).e) > 0
    decreases fuel, |segments| - i
  {
    if i == |segments| {
      DirectFailurePositive(fs, current);
      if C.TerminalNoFollowResultFields(fs, current).Ok? &&
         FsNodeAt(fs, current).Symlink? {
        var target := FsNodeAt(fs, current).target;
        if (follow || directory) && target != "" && fuel > 0 {
          RawFailurePositive(fs, C.RawPathSegmentsFields(target), 0,
                             if IsAbsolutePath(target) then "/" else ParentPath(current),
                             seen + {current}, fuel - 1, follow, missing,
                             directory || C.HasTrailingSlash(target));
        }
      }
    } else if FsContainsPath(fs, current) && FsNodeAt(fs, current).Directory? &&
              !FixtureOwnerCanSearch(FsNodeAt(fs, current)) {
    } else if segments[i] == "." || segments[i] == ".." {
      DirectFailurePositive(fs, current);
      if C.TerminalNoFollowResultFields(fs, current).Ok? {
        match FsNodeAt(fs, current)
        case Directory(_, _, _) =>
          RawFailurePositive(fs, segments, i + 1,
                             if segments[i] == ".." then ParentPath(current) else current,
                             seen, fuel, follow, missing, directory);
        case Symlink(target, _, _, _) =>
          if target != "" && fuel > 0 {
            RawFailurePositive(fs, C.RawPathSegmentsFields(target) + segments[i..], 0,
                               if IsAbsolutePath(target) then "/" else ParentPath(current),
                               seen + {current}, fuel - 1, follow, missing, directory);
          }
        case _ =>
      }
    } else {
      var next := AppendPath(current, segments[i]);
      DirectFailurePositive(fs, next);
      if C.DirectNoFollowResultFields(fs, next).Ok? {
        match FsNodeAt(fs, next)
        case Directory(_, _, _) =>
          RawFailurePositive(fs, segments, i + 1, next, seen, fuel,
                             follow, missing, directory);
        case Symlink(target, _, _, _) =>
          if !(i + 1 == |segments| && !follow && !directory) &&
             target != "" && fuel > 0 {
            var remaining := segments[i + 1..];
            RawFailurePositive(fs, C.RawPathSegmentsFields(target) + remaining, 0,
                               if IsAbsolutePath(target) then "/" else ParentPath(next),
                               seen + {next}, fuel - 1, follow, missing,
                               directory || (|remaining| == 0 && C.HasTrailingSlash(target)));
          }
        case _ =>
      }
    }
  }

  lemma OpenDirFailureClassification(fs: FileSystem, path: Path)
    ensures C.OpenDirFailureErrFields(fs, path) >= 0
    ensures (C.OpenDirFailureErrFields(fs, path) == 0) ==
            (C.ResolvePathForMetadataFields(fs, path, true).Ok? &&
             FsNodeAt(fs, C.ResolvePathForMetadataFields(fs, path, true).v).Directory?)
  {
    RawFailurePositive(fs, C.RawPathSegmentsFields(path), 0,
                       if IsAbsolutePath(path) then "/" else "", {}, SYMLINK_MAX_DEPTH,
                       true, false, C.HasTrailingSlash(path));
  }
}
