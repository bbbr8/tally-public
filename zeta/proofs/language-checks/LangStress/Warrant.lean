import LangStress.Tokens
/-!
# Warrant — reference semantics (assumption-based truth maintenance)

Premises are nodes `0 … P-1`; an environment is a bitmask over premises.
`holds s n` : node `n` is derivable when exactly the premises in `s` are available.
`label n`   : the environments under which `n` holds, consistent (no nogood inside), and minimal.
`critical`  : the minimal premise sets of size ≤ 3 whose loss takes every environment of the label away.
These are written from the definitions, not from Warrant's propagation code.
-/
namespace LangStress.Warrant

structure Just where
  t : Nat
  ants : List Nat
  u : Nat

@[inline] def sub (a b : Nat) : Bool := (a &&& b) == a

def consistent (gs : List Nat) (s : Nat) : Bool := gs.all fun g => !(sub g s)

/-- one round of forward chaining -/
def step (js : List Just) (s d : Nat) : Nat :=
  js.foldl (fun acc j => if sub j.u s && j.ants.all (fun a => d.testBit a) then acc ||| (1 <<< j.t) else acc) d

def iter (js : List Just) (s : Nat) : Nat → Nat → Nat
  | 0, d => d
  | n + 1, d => iter js s n (step js s d)

/-- `N + 1` rounds reach the fixpoint: each round adds a node or changes nothing. -/
def closure (N : Nat) (js : List Just) (s : Nat) : Nat := iter js s (N + 1) s

def holds (N : Nat) (js : List Just) (s n : Nat) : Bool := (closure N js s).testBit n

def label (P N : Nat) (gs : List Nat) (js : List Just) (avoid n : Nat) : List Nat :=
  (List.range (2 ^ P)).filter fun s =>
    (s &&& avoid) == 0 && consistent gs s && holds N js s n &&
    (List.range (2 ^ P)).all fun t => !(sub t s && t != s && holds N js t n)

def critical (P : Nat) (lab : List Nat) : List Nat :=
  if lab.isEmpty then [] else
  let U := lab.foldl (· ||| ·) 0
  let hits := fun c => lab.all fun e => (c &&& e) != 0
  (List.range (2 ^ P)).filter fun c =>
    sub c U && popc c ≤ 3 && hits c &&
    (List.range (2 ^ P)).all fun t => !(sub t c && t != c && hits t)

/-- read the justifications -/
def readJusts (r : Rd) : Nat → List Just × Rd
  | 0 => ([], r)
  | k + 1 =>
    let (t, r) := r.nat
    let (ants, r) := r.counted
    let (u, r) := r.nat
    let (rest, r) := readJusts r k
    (⟨t, ants, u⟩ :: rest, r)

def readLabels (r : Rd) : Nat → List (List Nat) × Rd
  | 0 => ([], r)
  | k + 1 =>
    let (l, r) := r.counted
    let (rest, r) := readLabels r k
    (l :: rest, r)

/-- check one case line; returns the list of disagreements (empty = the runtime agrees with the reference) -/
def check (line : String) : String × List String := Id.run do
  let r := Rd.ofLine line
  let (_, r) := r.word
  let (seed, r) := r.nat
  let (P, r) := r.nat
  let (N, r) := r.nat
  let (gs, r) := r.counted
  let (nj, r) := r.nat
  let (js, r) := readJusts r nj
  let (labs, r) := readLabels r N
  let (crits, r) := readLabels r N
  let (_, r) := r.word
  let (retr, r) := r.nat
  let (labsR, _) := readLabels r N
  let mut bad : List String := []
  for n in List.range N do
    let want := label P N gs js 0 n
    let got := labs.getD n []
    if want != got then
      bad := bad ++ [s!"W_LABEL seed={seed} node={n} lean={want} warrant={got}"]
    if n ≥ P then
      let wc := critical P want
      let gc := crits.getD n []
      if wc != gc then
        bad := bad ++ [s!"W_CRITICAL seed={seed} node={n} lean={wc} warrant={gc}"]
    let wr := label P N gs js retr n
    let gr := labsR.getD n []
    if wr != gr then
      bad := bad ++ [s!"W_RETRACT seed={seed} node={n} retract={retr} lean={wr} warrant={gr}"]
  return (s!"W {seed}", bad)

end LangStress.Warrant
