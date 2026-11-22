/-
PrimeCheck.lean — trial division, as a function Lean can run compiled.
-/
namespace PnpFormal

/-- `noDiv p B` : no `d` with `2 ≤ d ≤ B` divides `p`. -/
def noDiv (p : Nat) : Nat → Bool
  | 0 => true
  | 1 => true
  | d + 2 => (p % (d + 2) != 0) && noDiv p (d + 1)

end PnpFormal
