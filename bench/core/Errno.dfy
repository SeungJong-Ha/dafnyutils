// Linux errno values used by the benchmark's modeled and native IO boundaries.
module Errnos {
  const EPERM: int := 1
  const ENOENT: int := 2
  const EINTR: int := 4
  const EIO: int := 5
  const EBADF: int := 9
  const ENOMEM: int := 12
  const EACCES: int := 13
  const EBUSY: int := 16
  const EEXIST: int := 17
  const EXDEV: int := 18
  const ENOTDIR: int := 20
  const EISDIR: int := 21
  const EINVAL: int := 22
  const ENFILE: int := 23
  const EMFILE: int := 24
  const EFBIG: int := 27
  const ENOSPC: int := 28
  const EROFS: int := 30
  const EMLINK: int := 31
  const EPIPE: int := 32
  const ENAMETOOLONG: int := 36
  const ENOTEMPTY: int := 39
  const ELOOP: int := 40
  const EOVERFLOW: int := 75
  const EOPNOTSUPP: int := 95
  const EDQUOT: int := 122
}
