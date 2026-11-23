/-! A tiny reader over one whitespace-separated case line. -/
namespace LangStress

structure Rd where
  toks : Array String
  i : Nat := 0
  deriving Inhabited

def Rd.ofLine (s : String) : Rd :=
  { toks := ((s.splitOn " ").filter (· ≠ "")).toArray }

def Rd.word (r : Rd) : String × Rd := (r.toks.getD r.i "", { r with i := r.i + 1 })

def Rd.nat (r : Rd) : Nat × Rd := ((r.toks.getD r.i "0").toNat!, { r with i := r.i + 1 })

/-- read `n` naturals -/
def Rd.nats (r : Rd) : Nat → List Nat × Rd
  | 0 => ([], r)
  | k + 1 =>
    let (x, r) := r.nat
    let (xs, r) := r.nats k
    (x :: xs, r)

/-- read a count followed by that many naturals -/
def Rd.counted (r : Rd) : List Nat × Rd :=
  let (n, r) := r.nat
  r.nats n

def popc (n : Nat) : Nat := (List.range 32).countP (n.testBit ·)

end LangStress
