include "../../core/World.dfy"
include "UniqSchema.dfy"
include "UniqCore.dfy"
include "UniqSpec.dfy"

module UniqProof {
  import BenchIO
  import BW = BenchWorld
  import Schema = UniqSchema
  import Core = UniqCore
  import Spec = UniqSpec

  lemma InputFromOperandsEq(operands: seq<string>)
    ensures Core.InputFromOperands(operands) ==
            Spec.InputFromOperands(operands)
  {
  }

  lemma CommandEq(raw: Schema.UniqCmdRaw)
    ensures Core.Command(raw) == Spec.Command(raw)
  {
    InputFromOperandsEq(raw.operands);
  }

  lemma LowerAsciiEq(ch: BW.RawByte)
    ensures Core.LowerAscii(ch) == Spec.LowerAscii(ch)
  {
  }

  lemma EqualFoldAsciiEq(a: BW.Bytes, b: BW.Bytes)
    ensures Core.EqualFoldAscii(a, b) == Spec.EqualFoldAscii(a, b)
    decreases |a|
  {
    if |a| == |b| && |a| > 0 {
      LowerAsciiEq(a[0]);
      LowerAsciiEq(b[0]);
      EqualFoldAsciiEq(a[1..], b[1..]);
    }
  }

  lemma CoreFieldStep(line: BW.Bytes, start: nat)
    requires start < |line|
    ensures Spec.FieldStep(
      line, start,
      Core.SkipNonBlanks(line, Core.SkipBlanks(line, start)))
  {
    var middle := Core.SkipBlanks(line, start);
    var end := Core.SkipNonBlanks(line, middle);
    assert Core.IsFieldBlank(line[start]) == Spec.IsFieldBlank(line[start]);
    if Core.IsFieldBlank(line[start]) {
      assert start < middle;
    } else {
      assert middle == start;
      assert start < end;
    }
    assert start < end <= |line|;
    if middle == end {
      assert middle == |line|;
    }
    assert forall i: nat :: start <= i < middle ==> Spec.IsFieldBlank(line[i]) by {
      forall i: nat | start <= i < middle
        ensures Spec.IsFieldBlank(line[i])
      {
      }
    }
    assert forall i: nat :: middle <= i < end ==> !Spec.IsFieldBlank(line[i]) by {
      forall i: nat | middle <= i < end
        ensures !Spec.IsFieldBlank(line[i])
      {
      }
    }
    assert end < |line| ==> Spec.IsFieldBlank(line[end]);
    assert start <= middle <= end;
    assert middle == end ==> end == |line|;
    assert start <= middle <= end &&
      (forall i: nat :: start <= i < middle ==> Spec.IsFieldBlank(line[i])) &&
      (forall i: nat :: middle <= i < end ==> !Spec.IsFieldBlank(line[i])) &&
      (middle == end ==> end == |line|) &&
      (end < |line| ==> Spec.IsFieldBlank(line[end]));
    assert Spec.FieldStepWitness(line, start, end, middle);
    assert Spec.FieldStep(line, start, end);
  }

  lemma {:isolate_assertions} SkipFieldsWitness(
    line: BW.Bytes, start: nat, count: nat
  )
    requires start <= |line|
    ensures Spec.FieldSkipFromRelation(
      line, start, count, Core.SkipFieldsIndex(line, start, count))
    decreases count
  {
    reveal Spec.FieldSkipFromRelation();
    if count == 0 || start == |line| {
      assert Spec.FieldSkipFromRelation(line, start, count, start) by {
        assert |[start]| == 1;
      }
    } else {
      var middle := Core.SkipBlanks(line, start);
      var end := Core.SkipNonBlanks(line, middle);
      CoreFieldStep(line, start);
      SkipFieldsWitness(line, end, count - 1);
      var tailCuts: seq<nat> :|
        1 <= |tailCuts| <= count &&
        tailCuts[0] == end &&
        (forall i: nat :: i + 1 < |tailCuts| ==>
          Spec.FieldStep(line, tailCuts[i], tailCuts[i + 1])) &&
        (|tailCuts| - 1 == count - 1 || tailCuts[|tailCuts| - 1] == |line|) &&
        Core.SkipFieldsIndex(line, end, count - 1) == tailCuts[|tailCuts| - 1];
      var cuts := [start] + tailCuts;
      assert forall i: nat :: i + 1 < |cuts| ==>
        Spec.FieldStep(line, cuts[i], cuts[i + 1]) by {
        forall i: nat | i + 1 < |cuts|
          ensures Spec.FieldStep(line, cuts[i], cuts[i + 1])
        {
        }
      }
      assert Spec.FieldSkipFromRelation(
        line, start, count, Core.SkipFieldsIndex(line, start, count));
    }
  }

  lemma {:isolate_assertions} FieldStepUnique(
    line: BW.Bytes, start: nat, first: nat, second: nat
  )
    requires Spec.FieldStep(line, start, first)
    requires Spec.FieldStep(line, start, second)
    ensures first == second
  {
    reveal Spec.FieldStep();
    var middle1: nat :| Spec.FieldStepWitness(line, start, first, middle1);
    var middle2: nat :| Spec.FieldStepWitness(line, start, second, middle2);
    reveal Spec.FieldStepWitness();
    if middle1 < middle2 {
      assert middle1 < first;
      assert Spec.IsFieldBlank(line[middle1]);
      assert !Spec.IsFieldBlank(line[middle1]);
    }
    if middle2 < middle1 {
      assert middle2 < second;
      assert Spec.IsFieldBlank(line[middle2]);
      assert !Spec.IsFieldBlank(line[middle2]);
    }
    assert middle1 == middle2;
    if first < second {
      assert first < |line|;
      assert middle1 < first;
      assert Spec.IsFieldBlank(line[first]);
      assert !Spec.IsFieldBlank(line[first]);
    }
    if second < first {
      assert second < |line|;
      assert middle2 < second;
      assert Spec.IsFieldBlank(line[second]);
      assert !Spec.IsFieldBlank(line[second]);
    }
  }

  lemma {:isolate_assertions} FieldSkipCanonical(
    line: BW.Bytes, start: nat, count: nat, cut: nat
  )
    requires start <= |line|
    requires Spec.FieldSkipFromRelation(line, start, count, cut)
    ensures cut == Core.SkipFieldsIndex(line, start, count)
    decreases count
  {
    reveal Spec.FieldSkipFromRelation();
    var cuts: seq<nat> :|
      1 <= |cuts| <= count + 1 &&
      cuts[0] == start &&
      (forall i: nat :: i + 1 < |cuts| ==>
        Spec.FieldStep(line, cuts[i], cuts[i + 1])) &&
      (|cuts| - 1 == count || cuts[|cuts| - 1] == |line|) &&
      cut == cuts[|cuts| - 1];
    if count == 0 || start == |line| {
      if |cuts| > 1 {
        assert Spec.FieldStep(line, start, cuts[1]);
        reveal Spec.FieldStep();
        assert start < cuts[1] <= |line|;
      }
      assert |cuts| == 1;
    } else {
      assert |cuts| > 1;
      var end := Core.SkipNonBlanks(line, Core.SkipBlanks(line, start));
      CoreFieldStep(line, start);
      FieldStepUnique(line, start, end, cuts[1]);
      var tailCuts := cuts[1..];
      assert Spec.FieldSkipFromRelation(line, end, count - 1, cut) by {
        assert forall i: nat :: i + 1 < |tailCuts| ==>
          Spec.FieldStep(line, tailCuts[i], tailCuts[i + 1]) by {
          forall i: nat | i + 1 < |tailCuts|
            ensures Spec.FieldStep(line, tailCuts[i], tailCuts[i + 1])
          {
          }
        }
      }
      FieldSkipCanonical(line, end, count - 1, cut);
    }
  }

  lemma {:isolate_assertions} FieldSkipRelationCanonical(
    line: BW.Bytes, count: nat, suffix: BW.Bytes
  )
    requires Spec.FieldSkipRelation(line, count, suffix)
    ensures suffix == line[Core.SkipFieldsIndex(line, 0, count)..]
  {
    reveal Spec.FieldSkipRelation();
    var cut: nat :|
      Spec.FieldSkipFromRelation(line, 0, count, cut) &&
      cut <= |line| &&
      suffix == line[cut..];
    FieldSkipCanonical(line, 0, count, cut);
  }

  lemma LinesEqualEq(
    cmd: Schema.UniqCmd,
    a: BW.Bytes,
    b: BW.Bytes
  )
    ensures Core.LinesEqual(cmd, a, b) ==
            Spec.LinesEqual(cmd, a, b)
  {
    var leftCut := Core.SkipFieldsIndex(a, 0, cmd.skipFields);
    var rightCut := Core.SkipFieldsIndex(b, 0, cmd.skipFields);
    SkipFieldsWitness(a, 0, cmd.skipFields);
    SkipFieldsWitness(b, 0, cmd.skipFields);
    assert Spec.FieldSkipRelation(a, cmd.skipFields, a[leftCut..]);
    assert Spec.FieldSkipRelation(b, cmd.skipFields, b[rightCut..]);
    EqualFoldAsciiEq(a[leftCut..], b[rightCut..]);
    reveal Spec.LinesEqual();
    if Spec.LinesEqual(cmd, a, b) {
      var left: BW.Bytes, right: BW.Bytes :|
        Spec.FieldSkipRelation(a, cmd.skipFields, left) &&
        Spec.FieldSkipRelation(b, cmd.skipFields, right) &&
        (if cmd.ignoreCase then Spec.EqualFoldAscii(left, right) else left == right);
      FieldSkipRelationCanonical(a, cmd.skipFields, left);
      FieldSkipRelationCanonical(b, cmd.skipFields, right);
    }
  }

  lemma EqualFoldAsciiReflexive(line: BW.Bytes)
    ensures Spec.EqualFoldAscii(line, line)
    decreases |line|
  {
    reveal Spec.EqualFoldAscii();
    if |line| > 0 {
      EqualFoldAsciiReflexive(line[1..]);
    }
  }

  lemma LinesEqualReflexive(
    cmd: Schema.UniqCmd,
    line: BW.Bytes
  )
    ensures Spec.LinesEqual(cmd, line, line)
  {
    reveal Spec.LinesEqual();
    SkipFieldsWitness(line, 0, cmd.skipFields);
    var suffix := line[Core.SkipFieldsIndex(line, 0, cmd.skipFields)..];
    assert Spec.FieldSkipRelation(line, cmd.skipFields, suffix);
    if cmd.ignoreCase {
      EqualFoldAsciiReflexive(suffix);
    }
  }

  ghost function ShiftCuts(cuts: seq<nat>, amount: nat): seq<nat>
  {
    seq(|cuts|, i requires 0 <= i < |cuts| => cuts[i] + amount)
  }

  lemma ShiftCutsIndex(cuts: seq<nat>, amount: nat, i: nat)
    requires i < |cuts|
    ensures ShiftCuts(cuts, amount)[i] == cuts[i] + amount
  {
  }

  lemma PrependSlice<T>(
    head: seq<T>,
    tail: seq<T>,
    start: nat,
    end: nat
  )
    requires start <= end <= |tail|
    ensures (head + tail)[
            |head| + start..|head| + end
            ] == tail[start..end]
  {
  }

  lemma {:isolate_assertions} PrependByteFragment(
    head: BW.Bytes,
    tailFragments: seq<BW.Bytes>,
    tail: BW.Bytes,
    tailCuts: seq<nat>
  )
    requires Spec.FragmentsConcatenate(
               tailFragments, tail, tailCuts
             )
    ensures Spec.FragmentsConcatenate(
              [head] + tailFragments,
              head + tail,
              [0] + ShiftCuts(tailCuts, |head|)
            )
  {
    reveal Spec.FragmentsConcatenate();
    forall i: nat {:trigger ([0] + ShiftCuts(
      tailCuts, |head|
      ))[i]} | i < |[head] + tailFragments|
      ensures ([0] + ShiftCuts(tailCuts, |head|))[i] <=
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] &&
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] <=
              |head + tail| &&
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] ==
              ([0] + ShiftCuts(tailCuts, |head|))[i] +
              |([head] + tailFragments)[i]| &&
              (head + tail)[
              ([0] + ShiftCuts(tailCuts, |head|))[i]..
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1]
              ] == ([head] + tailFragments)[i]
    {
      ShiftCutsIndex(tailCuts, |head|, i);
      if i > 0 {
        ShiftCutsIndex(tailCuts, |head|, i - 1);
        var k := i - 1;
        PrependSlice(head, tail, tailCuts[k], tailCuts[k + 1]);
      }
    }
  }

  lemma {:isolate_assertions} PrependRecordRun(
    head: seq<BW.Bytes>,
    tailRuns: seq<seq<BW.Bytes>>,
    tail: seq<BW.Bytes>,
    tailCuts: seq<nat>
  )
    requires |head| > 0
    requires Spec.RecordsConcatenate(tailRuns, tail, tailCuts)
    ensures Spec.RecordsConcatenate(
              [head] + tailRuns,
              head + tail,
              [0] + ShiftCuts(tailCuts, |head|)
            )
  {
    reveal Spec.RecordsConcatenate();
    forall i: nat {:trigger ([0] + ShiftCuts(
      tailCuts, |head|
      ))[i]} | i < |[head] + tailRuns|
      ensures ([0] + ShiftCuts(tailCuts, |head|))[i] <=
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] &&
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] <=
              |head + tail| &&
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] ==
              ([0] + ShiftCuts(tailCuts, |head|))[i] +
              |([head] + tailRuns)[i]| &&
              (head + tail)[
              ([0] + ShiftCuts(tailCuts, |head|))[i]..
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1]
              ] == ([head] + tailRuns)[i]
    {
      ShiftCutsIndex(tailCuts, |head|, i);
      if i > 0 {
        ShiftCutsIndex(tailCuts, |head|, i - 1);
        var k := i - 1;
        PrependSlice(head, tail, tailCuts[k], tailCuts[k + 1]);
      }
    }
  }

  lemma LinesFromWitness(
    data: BW.Bytes,
    current: BW.Bytes
  ) returns (
      terminated: seq<bool>,
      fragments: seq<BW.Bytes>,
      cuts: seq<nat>
    )
    requires forall j: nat :: j < |current| ==> current[j] != '\n'
    ensures Spec.RecordPartitionWitnessRelation(
              current + data,
              Core.LinesFrom(data, current),
              terminated,
              fragments,
              cuts
            )
    decreases |data|
  {
    var lines := Core.LinesFrom(data, current);
    if |data| == 0 {
      if |current| == 0 {
        terminated := [];
        fragments := [];
        cuts := [0];
      } else {
        terminated := [false];
        fragments := [current];
        cuts := [0, |current|];
      }
      reveal Spec.RecordPartitionWitnessRelation();
      reveal Spec.FragmentsConcatenate();
    } else if data[0] == '\n' {
      var tailTerminated, tailFragments, tailCuts :=
        LinesFromWitness(data[1..], []);
      var head := current + ['\n'];
      terminated := [true] + tailTerminated;
      fragments := [head] + tailFragments;
      cuts := [0] + ShiftCuts(tailCuts, |head|);
      PrependByteFragment(head, tailFragments, data[1..], tailCuts);
      reveal Spec.RecordPartitionWitnessRelation();
      assert forall i: nat | i < |lines| ::
          |fragments[i]| > 0 &&
          fragments[i] ==
          lines[i] + (if terminated[i] then ['\n'] else []) &&
          (forall j: nat :: j < |lines[i]| ==> lines[i][j] != '\n') &&
          (i + 1 < |lines| ==> terminated[i]) by {
        forall i: nat | i < |lines|
          ensures |fragments[i]| > 0 &&
                  fragments[i] ==
                  lines[i] + (if terminated[i] then ['\n'] else []) &&
                  (forall j: nat ::
                     j < |lines[i]| ==> lines[i][j] != '\n') &&
                  (i + 1 < |lines| ==> terminated[i])
        {
        }
      }
    } else {
      terminated, fragments, cuts :=
        LinesFromWitness(data[1..], current + [data[0]]);
    }
  }

  lemma LinesWitness(data: BW.Bytes) returns (
      terminated: seq<bool>,
      fragments: seq<BW.Bytes>,
      cuts: seq<nat>
    )
    ensures Spec.RecordPartitionWitnessRelation(
              data, Core.Lines(data), terminated, fragments, cuts
            )
    ensures Spec.RecordPartitionRelation(
              data, Core.Lines(data), terminated
            )
  {
    terminated, fragments, cuts := LinesFromWitness(data, []);
    reveal Spec.RecordPartitionRelation();
    assert exists fs: seq<BW.Bytes>, cs: seq<nat> ::
        Spec.RecordPartitionWitnessRelation(
          data, Core.Lines(data), terminated, fs, cs
        ) by {
      assert Spec.RecordPartitionWitnessRelation(
          data, Core.Lines(data), terminated, fragments, cuts
        );
    }
  }

  lemma {:isolate_assertions} GroupsFromWitness(
    cmd: Schema.UniqCmd,
    rest: seq<BW.Bytes>,
    current: BW.Bytes,
    count: nat,
    currentRun: seq<BW.Bytes>
  ) returns (
      runs: seq<seq<BW.Bytes>>,
      cuts: seq<nat>
    )
    requires 1 <= count
    requires |currentRun| == count
    requires |currentRun| > 0
    requires currentRun[0] == current
    requires forall j: nat | j < |currentRun| ::
               Spec.LinesEqual(cmd, current, currentRun[j])
    ensures Spec.RunPartitionWitnessRelation(
              cmd,
              currentRun + rest,
              Core.GroupsFrom(cmd, rest, current, count),
              runs,
              cuts
            )
    decreases |rest|
  {
    var groups := Core.GroupsFrom(cmd, rest, current, count);
    if |rest| == 0 {
      runs := [currentRun];
      cuts := [0, |currentRun|];
      reveal Spec.RunPartitionWitnessRelation();
      reveal Spec.RecordsConcatenate();
    } else {
      LinesEqualEq(cmd, current, rest[0]);
      if Core.LinesEqual(cmd, current, rest[0]) {
        assert forall j: nat | j < |currentRun + [rest[0]]| ::
            Spec.LinesEqual(
              cmd, current, (currentRun + [rest[0]])[j]
            ) by {
          forall j: nat | j < |currentRun + [rest[0]]|
            ensures Spec.LinesEqual(
                      cmd, current, (currentRun + [rest[0]])[j]
                    )
          {
          }
        }
        runs, cuts := GroupsFromWitness(
          cmd,
          rest[1..],
          current,
          count + 1,
          currentRun + [rest[0]]
        );
        assert currentRun + rest ==
               (currentRun + [rest[0]]) + rest[1..];
      } else {
        LinesEqualReflexive(cmd, rest[0]);
        var tailRuns, tailCuts := GroupsFromWitness(
          cmd, rest[1..], rest[0], 1, [rest[0]]
        );
        runs := [currentRun] + tailRuns;
        cuts := [0] + ShiftCuts(tailCuts, |currentRun|);
        PrependRecordRun(
          currentRun, tailRuns, [rest[0]] + rest[1..], tailCuts
        );
        reveal Spec.RunPartitionWitnessRelation();
        assert currentRun + rest ==
               currentRun + ([rest[0]] + rest[1..]);
        assert forall i: nat | i < |groups| ::
            |runs[i]| > 0 &&
            groups[i].count == |runs[i]| &&
            groups[i].line == runs[i][0] &&
            (forall j: nat | j < |runs[i]| ::
               Spec.LinesEqual(cmd, groups[i].line, runs[i][j])) &&
            (i + 1 < |groups| ==>
               !Spec.LinesEqual(
                 cmd, groups[i].line, groups[i + 1].line
               )) by {
          forall i: nat | i < |groups|
            ensures |runs[i]| > 0 &&
                    groups[i].count == |runs[i]| &&
                    groups[i].line == runs[i][0] &&
                    (forall j: nat | j < |runs[i]| ::
                       Spec.LinesEqual(
                         cmd, groups[i].line, runs[i][j]
                       )) &&
                    (i + 1 < |groups| ==>
                       !Spec.LinesEqual(
                         cmd, groups[i].line, groups[i + 1].line
                       ))
          {
          }
        }
      }
    }
  }

  lemma GroupsWitness(
    cmd: Schema.UniqCmd,
    lines: seq<BW.Bytes>
  ) returns (
      runs: seq<seq<BW.Bytes>>,
      cuts: seq<nat>
    )
    ensures Spec.RunPartitionWitnessRelation(
              cmd, lines, Core.Groups(cmd, lines), runs, cuts
            )
    ensures Spec.RunPartitionRelation(
              cmd, lines, Core.Groups(cmd, lines)
            )
  {
    if |lines| == 0 {
      runs := [];
      cuts := [0];
      reveal Spec.RunPartitionWitnessRelation();
      reveal Spec.RecordsConcatenate();
    } else {
      LinesEqualReflexive(cmd, lines[0]);
      runs, cuts := GroupsFromWitness(
        cmd, lines[1..], lines[0], 1, [lines[0]]
      );
    }
    reveal Spec.RunPartitionRelation();
    assert exists rs: seq<seq<BW.Bytes>>, cs: seq<nat> ::
        Spec.RunPartitionWitnessRelation(
          cmd, lines, Core.Groups(cmd, lines), rs, cs
        ) by {
      assert Spec.RunPartitionWitnessRelation(
          cmd, lines, Core.Groups(cmd, lines), runs, cuts
        );
    }
  }

  lemma DigitCharEq(d: int)
    ensures Core.DigitChar(d) == Spec.DigitChar(d)
  {
  }

  lemma DigitsEq(n: nat)
    ensures Core.Digits(n) == Spec.Digits(n)
    decreases n
  {
    if n < 10 {
      DigitCharEq(n as int);
    } else {
      DigitsEq(n / 10);
      DigitCharEq((n % 10) as int);
    }
  }

  lemma PadLeftEq(text: BW.Bytes, width: int)
    ensures Core.PadLeft(text, width) == Spec.PadLeft(text, width)
    decreases width - |text|
  {
    if |text| < width {
      PadLeftEq([' '] + text, width);
    }
  }

  lemma CountPrefixEq(count: nat)
    ensures Core.CountPrefix(count) == Spec.CountPrefix(count)
  {
    DigitsEq(count);
    PadLeftEq(Core.Digits(count), 7);
  }

  lemma ShouldOutputGroupEq(
    cmd: Schema.UniqCmd,
    group: Spec.Group
  )
    ensures Core.ShouldOutputGroup(cmd, group) ==
            Spec.ShouldOutputGroup(cmd, group)
  {
  }

  lemma RenderGroupRelation(
    cmd: Schema.UniqCmd,
    group: Spec.Group
  )
    ensures Spec.GroupRenderRelation(
              cmd, group, Core.RenderGroup(cmd, group)
            )
  {
    ShouldOutputGroupEq(cmd, group);
    if Core.ShouldOutputGroup(cmd, group) &&
       cmd.countOccurrences {
      CountPrefixEq(group.count);
    }
    reveal Spec.GroupRenderRelation();
  }

  lemma RenderGroupsWitness(
    cmd: Schema.UniqCmd,
    groups: seq<Spec.Group>
  ) returns (
      fragments: seq<BW.Bytes>,
      cuts: seq<nat>
    )
    ensures |fragments| == |groups|
    ensures forall i: nat | i < |groups| ::
              Spec.GroupRenderRelation(cmd, groups[i], fragments[i])
    ensures Spec.FragmentsConcatenate(
              fragments, Core.RenderGroups(cmd, groups), cuts
            )
    decreases |groups|
  {
    if |groups| == 0 {
      fragments := [];
      cuts := [0];
      reveal Spec.FragmentsConcatenate();
    } else {
      var head := Core.RenderGroup(cmd, groups[0]);
      RenderGroupRelation(cmd, groups[0]);
      var tailFragments, tailCuts :=
        RenderGroupsWitness(cmd, groups[1..]);
      fragments := [head] + tailFragments;
      cuts := [0] + ShiftCuts(tailCuts, |head|);
      PrependByteFragment(
        head,
        tailFragments,
        Core.RenderGroups(cmd, groups[1..]),
        tailCuts
      );
      assert forall i: nat | i < |groups| ::
          Spec.GroupRenderRelation(
            cmd, groups[i], fragments[i]
          ) by {
        forall i: nat | i < |groups|
          ensures Spec.GroupRenderRelation(
                    cmd, groups[i], fragments[i]
                  )
        {
        }
      }
    }
  }

  lemma {:isolate_assertions} OutputRelationForCore(
    cmd: Schema.UniqCmd,
    data: BW.Bytes
  )
    ensures Spec.OutputRelation(
              cmd, data, Core.RenderData(cmd, data)
            )
  {
    var records := Core.Lines(data);
    var terminated, lineFragments, lineCuts := LinesWitness(data);
    var groups := Core.Groups(cmd, records);
    var runs, runCuts := GroupsWitness(cmd, records);
    var outputFragments, outputCuts :=
      RenderGroupsWitness(cmd, groups);
    reveal Spec.OutputWitnessRelation();
    assert Spec.OutputWitnessRelation(
        cmd,
        data,
        Core.RenderData(cmd, data),
        records,
        terminated,
        groups,
        outputFragments,
        outputCuts
      );
    reveal Spec.OutputRelation();
    assert exists rs: seq<BW.Bytes>,
        ts: seq<bool>,
        gs: seq<Spec.Group>,
        fs: seq<BW.Bytes>,
        cs: seq<nat> ::
        Spec.OutputWitnessRelation(
          cmd, data, Core.RenderData(cmd, data), rs, ts, gs, fs, cs
        ) by {
      assert Spec.OutputWitnessRelation(
          cmd,
          data,
          Core.RenderData(cmd, data),
          records,
          terminated,
          groups,
          outputFragments,
          outputCuts
        );
    }
  }

  twostate lemma InputTraceRefines(
    cmd: Schema.UniqCmd,
    io: BenchIO.IO,
    preStreams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
    new readResults: seq<BW.Result<BW.Bytes>>,
    new stdoutPart: BW.Bytes,
    new stderrPart: BW.Bytes,
    hadError: bool
  )
    requires preStreams == old(io.trustedStreams())
    requires Core.InputTraceRelation(
               cmd,
               old(io.fs()),
               old(io.stdin()),
               preStreams,
               readResults,
               stdoutPart,
               stderrPart,
               hadError
             )
    ensures Spec.InputTraceRelation(
              cmd, io, readResults, stdoutPart, stderrPart, hadError
            )
  {
    reveal Core.InputTraceRelation();
    reveal Core.OutputRelation();
    reveal Spec.InputTraceRelation();
    match cmd.input {
      case Stdin =>
        OutputRelationForCore(cmd, old(io.stdin()));
      case File(_) =>
        match readResults[0] {
          case Ok(data) =>
            OutputRelationForCore(cmd, data);
          case Err(_) =>
        }
    }
  }

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.UniqCmdRaw,
    io: BenchIO.IO,
    exit: int,
    new readResults: seq<BW.Result<BW.Bytes>>,
    new stdoutPart: BW.Bytes,
    new stderrPart: BW.Bytes,
    hadError: bool
  )
    requires Core.CoreSummary(
               raw, io, exit, readResults, stdoutPart, stderrPart, hadError
             )
    ensures Spec.Spec(raw, io, exit)
  {
    reveal Core.CoreSummary();
    reveal Spec.Spec();
    CommandEq(raw);
    var cmd := Core.Command(raw);
    if cmd.mode == Schema.ModeRun {
      InputTraceRefines(
        cmd,
        io,
        old(io.trustedStreams()),
        readResults,
        stdoutPart,
        stderrPart,
        hadError
      );
    }
  }
}
