# `Cond` followed by a send

Use distinct roles A and B, no local actions, trivial initial stores and
empty FIFOs. At both roles use the same constructors: announce the Boolean
`true` at A, then send unit from A to B for either choice.

| Observation | Expected outcome |
| --- | --- |
| Initial source actions | Only the announcement by A |
| After the source announcement | A may send unit before or after B receives the choice |
| Final source state | B has received both values, in source order |
| Outstanding source steps | Every reachable nonfinal state has an action |
| Generated owner endpoint | Continuation can send `"()"` before broadcasting `"True"` |
| Generated peer endpoint | Waits for a Boolean at `(A,B,Root)` |
| Queue after send then broadcast | `["()", "True"]` at `(A,B,Root)` |
| Residual network | A returned, B cannot decode the head, no other action, not final |
| Failed obligations | The send-first prefix has no source history in action order; the stuck two-action execution has no stuck source witness |

This is a diagnostic for the unmodified generated endpoints. A fixture
that replaces the sender or supplies a different decoder would not establish
the counterexample.
