import Std

namespace RiemannKeys

/-- Test divisibility by the integers from two through the square root. -/
def primeByTrialDivision (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range (n.sqrt + 1)).all fun d =>
    decide (d < 2) || decide (n % d ≠ 0)

/-- An independent finite check for the Gauss namesake example. -/
theorem primesThrough1000 :
    ((List.range 1001).filter primeByTrialDivision).length = 168 := by native_decide

/-- Cross-multiply the four nonzero denominators in the s = 2 Euler product. -/
theorem eulerProductThrough10 :
    ([2, 3, 5, 7] : List Nat).foldl (fun acc p => acc * (p*p)) 1 * 768
      = 1225 * ([2, 3, 5, 7] : List Nat).foldl (fun acc p => acc * (p*p - 1)) 1 := by decide

#print axioms primesThrough1000
#print axioms eulerProductThrough10

end RiemannKeys
