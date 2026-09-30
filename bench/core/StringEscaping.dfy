include "World.dfy"

// Shared byte-based renderers for GNU-style diagnostic strings and filenames.
// Text callers pass `Utf8.Encode(text)`; these helpers consume `BW.Bytes` and do
// not encode Unicode themselves.
// `SpecLocaleQuoteBytes` produces fixed C-locale display quoting; it does not
// select behavior from the runtime locale. `SpecQuoteAfBytes` always applies
// shell quoting, while `SpecQuoteFBytes` quotes conditionally and forces quotes
// for a colon. Their `Af` and `F` names mirror GNU's `quoteaf` and `quotef`.
// Byte-escape helpers build bodies; the rendering entry points add delimiters.
module StringEscaping {
  import BW = BenchWorld

  // Classifies printable ASCII bytes as 0x20 through 0x7e for C-locale escaping.
  function SpecCPrintableByte(byte: char): bool
  {
    0x20 <= byte as int <= 0x7e
  }

  // Converts an octal digit value to its character; callers use 0 through 7.
  // The final branch is the existing fallback to `'7'` for other values.
  function SpecOctDigit(value: int): char
  {
    if value == 0 then '0'
    else if value == 1 then '1'
    else if value == 2 then '2'
    else if value == 3 then '3'
    else if value == 4 then '4'
    else if value == 5 then '5'
    else if value == 6 then '6'
    else '7'
  }

  // Writes one byte as a backslash and exactly three octal digits, e.g. 0x1b
  // becomes `\033`; fixed width keeps following digits from merging into it.
  function SpecOctalEscape(byte: char): BW.Bytes
  {
    var value := byte as int;
    ['\\', SpecOctDigit((value / 64) % 8), SpecOctDigit((value / 8) % 8), SpecOctDigit(value % 8)]
  }

  // Uses C-style short names for bell, backspace, form feed, newline, carriage
  // return, tab, and vertical tab; returns `[]` when no named escape applies.
  function SpecNamedEscape(byte: char): BW.Bytes
  {
    if byte == 7 as char then "\\a"
    else if byte == 8 as char then "\\b"
    else if byte == 12 as char then "\\f"
    else if byte == '\n' then "\\n"
    else if byte == '\r' then "\\r"
    else if byte == '\t' then "\\t"
    else if byte == 11 as char then "\\v"
    else []
  }

  // Chooses a named control escape when available, otherwise the three-digit
  // octal form used inside ANSI-C shell quotes; this emits no quote delimiters.
  function SpecAnsiEscape(byte: char): BW.Bytes
  {
    var named := SpecNamedEscape(byte);
    if named != [] then named else SpecOctalEscape(byte)
  }

  // Marks bytes outside printable ASCII for an ANSI-C shell segment; printable
  // apostrophes are handled separately by the shell-tail renderer.
  function SpecNeedsAnsiEscape(byte: char): bool
  {
    !SpecCPrintableByte(byte)
  }

  // Escapes one byte for a C-style double-quoted body, including quote and
  // backslash escapes; it does not add the surrounding double quotes.
  function SpecCQuoteByte(byte: char): BW.Bytes
  {
    var named := SpecNamedEscape(byte);
    if named != [] then named
    else if byte == '\\' then "\\\\"
    else if byte == '"' then "\\\""
    else if SpecCPrintableByte(byte) then [byte]
    else SpecOctalEscape(byte)
  }

  // Concatenates the C-style escaped body for a byte sequence without adding
  // delimiters; `SpecDoubleQuote` supplies those around this result.
  function SpecCQuoteBytes(bytes: BW.Bytes): BW.Bytes
    decreases |bytes|
  {
    if |bytes| == 0 then
      []
    else
      SpecCQuoteByte(bytes[0]) + SpecCQuoteBytes(bytes[1..])
  }

  // Encloses a C-style escaped body in double quotes, as used by the GNU
  // shell-quoting shortcut when an apostrophe cannot stay in single quotes.
  function SpecDoubleQuote(bytes: BW.Bytes): BW.Bytes
  {
    "\"" + SpecCQuoteBytes(bytes) + "\""
  }

  // Tests eligibility for the GNU double-quote shortcut, not general safety
  // for unquoted shell text: spaces and apostrophes pass this test. `atStart`
  // means first byte of the whole input; `singleton` means the whole input
  // has one byte.
  function SpecShellCompatibleByte(byte: char, atStart: bool, singleton: bool): bool
  {
    if byte == '?' || byte == '\\' then
      false
    else if byte == '{' || byte == '}' then
      singleton
    else if byte == '#' || byte == '~' then
      atStart
    else if byte == ' ' || byte == '\'' then
      true
    else if byte == '!' || byte == '"' || byte == '$' || byte == '&' ||
            byte == '(' || byte == ')' || byte == '*' || byte == ';' ||
            byte == '<' || byte == '=' || byte == '>' || byte == '[' ||
            byte == '^' || byte == '`' || byte == '|' then
      false
    else
      SpecCPrintableByte(byte)
  }

  // Checks a suffix for shortcut eligibility, treating every byte as neither
  // the first byte nor the sole byte of the whole input; the empty suffix passes.
  function SpecShellCompatibleTail(bytes: BW.Bytes): bool
    decreases |bytes|
  {
    |bytes| == 0 ||
    (SpecShellCompatibleByte(bytes[0], false, false) &&
     SpecShellCompatibleTail(bytes[1..]))
  }

  // Checks all bytes for double-quote-shortcut eligibility, supplying the true
  // first-byte and whole-input-singleton facts only for the first byte.
  function SpecAllShellCompatible(bytes: BW.Bytes): bool
  {
    |bytes| == 0 ||
    (SpecShellCompatibleByte(bytes[0], true, |bytes| == 1) &&
     SpecShellCompatibleTail(bytes[1..]))
  }

  // Reports whether the input contains an apostrophe; `SpecQuoteAfBytes` uses
  // this to decide whether the all-compatible double-quote shortcut applies.
  function SpecContainsApostrophe(bytes: BW.Bytes): bool
  {
    '\'' in bytes
  }

  // Escapes the bytes after an opening single quote and appends the final quote.
  // `ansi` tracks whether an ANSI-C `$'...'` segment is active: controls enter
  // one, printable bytes leave it, and apostrophes splice as `'\''`.
  function SpecShellEscapeTail(bytes: BW.Bytes, ansi: bool): BW.Bytes
    decreases |bytes|
  {
    if |bytes| == 0 then
      "'"
    else
      var byte := bytes[0];
      if byte == '\'' then
        "'\\''" + SpecShellEscapeTail(bytes[1..], false)
      else if SpecNeedsAnsiEscape(byte) then
        (if ansi then [] else "'$'") + SpecAnsiEscape(byte) +
        SpecShellEscapeTail(bytes[1..], true)
      else
        (if ansi then "''" else []) + [byte] +
        SpecShellEscapeTail(bytes[1..], false)
  }

  // Always renders a shell-quoted byte string, including empty input. If an
  // apostrophe occurs and all bytes pass the shortcut test, it uses double
  // quotes; otherwise it uses single quotes with ANSI-C segments as needed.
  // For example, `can't` becomes `"can't"`, and `a`, newline, `b` becomes
  // `'a'$'\n''b'`.
  function SpecQuoteAfBytes(bytes: BW.Bytes): BW.Bytes
  {
    if SpecContainsApostrophe(bytes) && SpecAllShellCompatible(bytes) then
      SpecDoubleQuote(bytes)
    else
      "'" + SpecShellEscapeTail(bytes, false)
  }

  // Tests whether a byte forces conditional shell quoting; colon always does,
  // while `#`/`~` force only at the start and braces only for a singleton.
  function SpecShellQuoteTriggerByte(byte: char, atStart: bool, singleton: bool): bool
  {
    !SpecCPrintableByte(byte) ||
    byte == '\\' || byte == '\'' || byte == '?' || byte == ':' ||
    byte == ' ' || byte == '!' || byte == '"' || byte == '$' ||
    byte == '&' || byte == '(' || byte == ')' || byte == '*' ||
    byte == ';' || byte == '<' || byte == '=' || byte == '>' ||
    byte == '[' || byte == '^' || byte == '`' || byte == '|' ||
    ((byte == '#' || byte == '~') && atStart) ||
    ((byte == '{' || byte == '}') && singleton)
  }

  // Searches the suffix after the first byte for any conditional-quoting
  // trigger, with all suffix bytes treated as noninitial and nonsingleton.
  function SpecHasShellQuoteTriggerTail(bytes: BW.Bytes): bool
    decreases |bytes|
  {
    |bytes| != 0 &&
    (SpecShellQuoteTriggerByte(bytes[0], false, false) ||
     SpecHasShellQuoteTriggerTail(bytes[1..]))
  }

  // Searches the whole input for conditional-quoting triggers, passing the
  // actual start and whole-input-singleton facts for its first byte.
  function SpecHasShellQuoteTrigger(bytes: BW.Bytes): bool
  {
    |bytes| != 0 &&
    (SpecShellQuoteTriggerByte(bytes[0], true, |bytes| == 1) ||
     SpecHasShellQuoteTriggerTail(bytes[1..]))
  }

  // Implements GNU-style `quotef` behavior: empty input or any trigger (such
  // as the colon in `a:b`) uses always-shell-quoting; otherwise bytes pass through.
  function SpecQuoteFBytes(bytes: BW.Bytes): BW.Bytes
  {
    if |bytes| == 0 || SpecHasShellQuoteTrigger(bytes) then
      SpecQuoteAfBytes(bytes)
    else
      bytes
  }

  // Escapes one byte in the fixed C-locale display body: named controls,
  // apostrophes, backslashes, printable ASCII, then fixed-width octal bytes.
  function SpecLocaleQuoteByte(byte: char): BW.Bytes
  {
    var named := SpecNamedEscape(byte);
    if named != [] then named
    else if byte == '\'' then "\\'"
    else if byte == '\\' then "\\\\"
    else if SpecCPrintableByte(byte) then [byte]
    else SpecOctalEscape(byte)
  }

  // Builds only the fixed C-locale escaped display body; `SpecLocaleQuoteBytes`
  // adds its surrounding apostrophes.
  function SpecLocaleQuoteBody(bytes: BW.Bytes): BW.Bytes
    decreases |bytes|
  {
    if |bytes| == 0 then
      []
    else
      SpecLocaleQuoteByte(bytes[0]) + SpecLocaleQuoteBody(bytes[1..])
  }

  // Always encloses a fixed C-locale display body in apostrophes, including
  // plain text such as `abc`, which becomes `'abc'`.
  function SpecLocaleQuoteBytes(bytes: BW.Bytes): BW.Bytes
  {
    "'" + SpecLocaleQuoteBody(bytes) + "'"
  }

}
