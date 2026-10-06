module Results {
  datatype Result<T, E> = Ok(v: T) | Err(e: E) {
    predicate IsFailure() { Err? }

    function Extract(): T
      requires Ok?
    { v }

    function PropagateFailure<U>(): Result<U, E>
      requires Err?
    { Err(e) }

    function Map<U>(f: T -> U): Result<U, E>
    {
      match this
      case Ok(value) => Ok(f(value))
      case Err(error) => Err(error)
    }

    function Bind<U>(f: T -> Result<U, E>): Result<U, E>
    {
      match this
      case Ok(value) => f(value)
      case Err(error) => Err(error)
    }
  }
}
