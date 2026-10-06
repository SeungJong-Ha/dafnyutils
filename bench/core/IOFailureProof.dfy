include "IOContract.dfy"

module IOFailureProof {
  import Errno = Errnos
  import Result = Results
  import opened BenchWorld
  import C = IOContract

  // A source lookup that reports ENOTDIR cannot be replaced by the empty-target ENOENT.
  lemma HardLinkSourceNotDirectoryRejectsMissingTargetError(
    fs: FileSystem, now: int, source: Path, target: Path,
    observations: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    after: FileSystem
  )
    requires (0 as char) !in source && (0 as char) !in target
    requires C.ResolvePathForMetadataFields(fs, source, false) == Result.Err(NotDirectory)
    ensures !C.CreateHardLinkSpec(fs, now, observations, after, source, target, false, Errno.ENOENT)
    ensures !C.CreateHardLinkSpec(fs, now, observations, after, source, target, true, 0)
  {
    assert C.HardLinkFailureErrnosFields(fs, source, target) ==
           C.NativeLookupFaultErrnos + {Errno.ENOTDIR};
  }

  // Every API using a validated filesystem result excludes failure with errno zero.
  lemma FilesystemFailureHasPositiveErrno(
    request: TrustedFilesystemRequest, result: TrustedFilesystemResult
  )
    requires C.ValidFilesystemObservation(request, result)
    requires !result.ok
    ensures result.err > 0
  {
  }

  // Query failures cannot modify the filesystem behind a read-only API.
  lemma FailedQueryPreservesFilesystem(
    fs: FileSystem, path: Path, follow: bool, result: TrustedFilesystemResult
  )
    requires C.ValidFilesystemObservation(FilesystemQuery(fs, path, follow), result)
    ensures result.postFs == fs
  {
  }

  // Atomic failure cannot delete unrelated inode records or namespace entries.
  lemma AtomicFailurePreservesNamespace(
    request: TrustedFilesystemRequest, result: TrustedFilesystemResult
  )
    requires C.ValidFilesystemObservation(request, result)
    requires !result.ok && !request.FilesystemCreate? && !request.FilesystemAppend? && !request.FilesystemWrite?
    ensures result.postFs.namespace == request.preFs.namespace
    ensures result.postFs.inodes.Keys == request.preFs.inodes.Keys
  {
  }

  // Projecting a failed read retains its exact errno, stage and committed prefix.
  lemma ReadFailureProjectionPreservesOutcome(
    data: Bytes, err: int, stage: FileReadStage, message: string
  )
    requires err > 0
    ensures C.FileReadResultFromOutcome(data, err, stage, message) ==
            Result.Err(ReadFailure(err, message, data, stage))
    ensures C.IOErrorErrno(C.FileReadResultFromOutcome(data, err, stage, message).e) == err
    ensures C.ReadFailureData(C.FileReadResultFromOutcome(data, err, stage, message).e) == data
  {
  }
  // Binding a failure propagates the entire error, including partial-transfer evidence.
  lemma ResultFailurePropagation<T, U>(error: IOError, next: T -> IOResult<U>)
    ensures Result.Result<T, IOError>.Err(error).Bind(next) == Result.Result<U, IOError>.Err(error)
    ensures Result.Result<T, IOError>.Err(error).PropagateFailure<U>() == Result.Result<U, IOError>.Err(error)
  {
  }

  // Opening failure commits no bytes and preserves namespace entries.
  lemma FailedWriteOpenPreservesNamespace(
    fs: FileSystem, now: int, path: Path, data: Bytes, append: bool,
    err: int, committed: nat, after: FileSystem
  )
    requires C.WriteFileOutcomeFields(fs, now, path, data, append, false, err,
                                      committed, WriteOpenFailed, after)
    ensures committed == 0
    ensures after.namespace == fs.namespace && after.inodes.Keys == fs.inodes.Keys
  {
  }

  // A close failure follows a complete write and cannot erase its committed byte count.
  lemma FailedWriteCloseHasCompletePrefix(
    fs: FileSystem, now: int, path: Path, data: Bytes, append: bool,
    err: int, committed: nat, after: FileSystem
  )
    requires C.WriteFileOutcomeFields(fs, now, path, data, append, false, err,
                                      committed, WriteCloseFailed, after)
    ensures committed == |data| && err > 0
  {
  }

}
