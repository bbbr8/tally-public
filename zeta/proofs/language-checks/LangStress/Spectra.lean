import LangStress.Tokens
/-!
# Spectra — reference semantics for the tracing doctrines (exact rationals)

A deposit first repays what the bank lent on an earlier overdraft; only the rest is traceable money.
FIFO / LIFO / OWNER_FIRST / OWNER_LAST draw whole tranches in their doctrine's order.
PRO_RATA draws every origin in proportion to what it holds.
LIBR is NOT re-implemented: it is checked against OWNER_LAST, because the lowest-intermediate-balance
rule and owner-last tracing must give the owner the same dollars (others' money leaves first).
-/
namespace LangStress.Spectra

/-- slots: 0-3 origins, 4 overdraft, 5 owner (LIBR), 6 others (LIBR) -/
abbrev Vec := Array Rat

def zero : Vec := Array.replicate 7 0

def addAt (v : Vec) (i : Nat) (x : Rat) : Vec := v.set! i (v.getD i 0 + x)

structure Row where
  out : Bool
  o : Nat
  c : Rat

/-- tranche state: (origin, amount) in arrival order, plus bank debt -/
structure TState where
  tr : List (Nat × Rat) := []
  debt : Rat := 0

def isOwner (mask o : Nat) : Bool := o < 2 && mask.testBit o

/-- order of tranche positions for a doctrine: 0 FIFO 1 LIFO 3 OWNER_FIRST 4 OWNER_LAST -/
def order (d mask : Nat) (tr : List (Nat × Rat)) : List Nat :=
  let idx := List.range tr.length
  let own := idx.filter fun i => isOwner mask (tr.getD i (0, 0)).1
  let oth := idx.filter fun i => !isOwner mask (tr.getD i (0, 0)).1
  match d with
  | 0 => idx
  | 1 => idx.reverse
  | 3 => own ++ oth
  | _ => oth ++ own

def deposit (s : TState) (o : Nat) (c : Rat) : TState :=
  let repay := min s.debt c
  let c' := c - repay
  { tr := if c' > 0 then s.tr ++ [(o, c')] else s.tr, debt := s.debt - repay }

def draw (d mask : Nat) (s : TState) (x : Rat) : TState × Vec := Id.run do
  let mut amts := s.tr.toArray
  let mut need := x
  let mut v := zero
  for i in order d mask s.tr do
    if need > 0 then
      let (o, a) := amts.getD i (0, 0)
      let take := min need a
      if take > 0 then
        v := addAt v o take
        amts := amts.set! i (o, a - take)
        need := need - take
  let mut debt := s.debt
  if need > 0 then
    v := v.set! 4 need
    debt := debt + need
  return ({ tr := amts.toList.filter (fun t => t.2 > 0), debt }, v)

def runTranche (d mask : Nat) (rows : List Row) : List Vec × Vec := Id.run do
  let mut s : TState := {}
  let mut outs : List Vec := []
  for r in rows do
    if r.out then
      let (s', v) := draw d mask s r.c
      s := s'; outs := outs ++ [v]
    else s := deposit s r.o r.c
  let held := s.tr.foldl (fun h t => addAt h t.1 t.2) zero
  return (outs, held)

def runProRata (rows : List Row) : List Vec × Vec := Id.run do
  let mut pool : Vec := zero
  let mut debt : Rat := 0
  let mut outs : List Vec := []
  for r in rows do
    if r.out then
      let tot := (List.range 4).foldl (fun s i => s + pool.getD i 0) 0
      let take := min r.c tot
      let mut v := zero
      if tot > 0 then
        for i in List.range 4 do
          let part := pool.getD i 0 * take / tot
          v := addAt v i part
          pool := pool.set! i (pool.getD i 0 - part)
      let need := r.c - take
      if need > 0 then
        v := v.set! 4 need
        debt := debt + need
      outs := outs ++ [v]
    else
      let repay := min debt r.c
      debt := debt - repay
      pool := addAt pool r.o (r.c - repay)
  return (outs, pool)

/-- what LIBR must print, derived from the OWNER_LAST split -/
def libOfOwnerLast (mask : Nat) (v : Vec) : Vec :=
  let own := (List.range 4).foldl (fun s i => if isOwner mask i then s + v.getD i 0 else s) 0
  let oth := (List.range 4).foldl (fun s i => if isOwner mask i then s else s + v.getD i 0) 0
  ((zero.set! 4 (v.getD 4 0)).set! 5 own).set! 6 oth

def Rd.rat (r : Rd) : Rat × Rd :=
  let (sg, r) := r.nat
  let (n, r) := r.nat
  let (d, r) := r.nat
  let q : Rat := (n : Rat) / (d : Rat)
  (if sg == 1 then -q else q, r)

def readVec (r : Rd) : Vec × Rd := Id.run do
  let mut r := r
  let mut v := zero
  for i in List.range 7 do
    let (x, r') := Rd.rat r
    v := v.set! i x; r := r'
  return (v, r)

def names : List String := ["FIFO", "LIFO", "PRO_RATA", "OWNER_FIRST", "OWNER_LAST", "LIBR"]

def check (line : String) : String × List String := Id.run do
  let r := Rd.ofLine line
  let (_, r) := r.word
  let (seed, r) := r.nat
  let (mask, r) := r.nat
  let (n, r) := r.nat
  let (spec, r) := r.nats (3 * n)
  let rows : List Row := (List.range n).map fun i =>
    { out := spec.getD (3 * i) 0 == 1, o := spec.getD (3 * i + 1) 0, c := (spec.getD (3 * i + 2) 0 : Rat) }
  let nout := (rows.filter (·.out)).length
  let outRows := rows.filter (·.out)
  let mut r := r
  let mut bad : List String := []
  let (olOuts, olHeld) := runTranche 4 mask rows
  for d in List.range 6 do
    let (want, wheld) :=
      if d == 2 then runProRata rows
      else if d == 5 then (olOuts.map (libOfOwnerLast mask), libOfOwnerLast mask olHeld)
      else runTranche d mask rows
    for j in List.range nout do
      let (got, r') := readVec r
      r := r'
      let w := want.getD j zero
      if w != got then
        bad := bad ++ [s!"S_SPLIT seed={seed} doctrine={names.getD d "?"} outflow={j} lean={w.toList} spectra={got.toList}"]
      let total := got.foldl (· + ·) 0
      if total != (outRows.getD j ⟨true, 0, 0⟩).c then
        bad := bad ++ [s!"S_CONSERVATION seed={seed} doctrine={names.getD d "?"} outflow={j} split_total={total} outflow={(outRows.getD j ⟨true, 0, 0⟩).c}"]
      if got.any (· < 0) then
        bad := bad ++ [s!"S_NEGATIVE seed={seed} doctrine={names.getD d "?"} outflow={j} spectra={got.toList}"]
    let (gh, r') := readVec r
    r := r'
    -- held: the overdraft slot is not a holding
    let wh := wheld.set! 4 0
    if wh != gh then
      bad := bad ++ [s!"S_HELD seed={seed} doctrine={names.getD d "?"} lean={wh.toList} spectra={gh.toList}"]
  return (s!"S {seed}", bad)

end LangStress.Spectra
