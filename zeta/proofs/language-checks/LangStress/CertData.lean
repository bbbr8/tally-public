import LangStress.Warrant
import LangStress.CaseLog
import LangStress.Concord
import LangStress.Spectra
/-! Recorded runtime answers, embedded at compile time, and the functions that re-check them. -/
namespace LangStress.Cert

def agrees (line : String) : Bool :=
  if line.startsWith "W " then (Warrant.check line).2.isEmpty
  else if line.startsWith "C " then (CaseLog.check line).2.isEmpty
  else if line.startsWith "K " then (Concord.check line).2.isEmpty
  else if line.startsWith "S " then (Spectra.check line).2.isEmpty
  else false

def cases (t : String) : List String := (t.splitOn "\n").filter (·.length ≥ 3)

/-- (programs, programs whose recorded answer disagrees with the reference semantics) -/
def tally (t : String) : Nat × Nat :=
  let cs := cases t
  (cs.length, (cs.filter (fun l => !agrees l)).length)

def warrant_before_A : String := include_str "../cert/warrant_before_A.txt"
def warrant_after_A : String := include_str "../cert/warrant_after_A.txt"
def caselog_before_A : String := include_str "../cert/caselog_before_A.txt"
def caselog_after_A : String := include_str "../cert/caselog_after_A.txt"
def spectra_before_A : String := include_str "../cert/spectra_before_A.txt"
def spectra_after_A : String := include_str "../cert/spectra_after_A.txt"
def concord_after_A : String := include_str "../cert/concord_after_A.txt"
def warrant_before_B : String := include_str "../cert/warrant_before_B.txt"
def warrant_after_B : String := include_str "../cert/warrant_after_B.txt"
def caselog_before_B : String := include_str "../cert/caselog_before_B.txt"
def caselog_after_B : String := include_str "../cert/caselog_after_B.txt"
def spectra_before_B : String := include_str "../cert/spectra_before_B.txt"
def spectra_after_B : String := include_str "../cert/spectra_after_B.txt"
def concord_after_B : String := include_str "../cert/concord_after_B.txt"
def warrant_before_C : String := include_str "../cert/warrant_before_C.txt"
def warrant_after_C : String := include_str "../cert/warrant_after_C.txt"
def caselog_before_C : String := include_str "../cert/caselog_before_C.txt"
def caselog_after_C : String := include_str "../cert/caselog_after_C.txt"
def spectra_before_C : String := include_str "../cert/spectra_before_C.txt"
def spectra_after_C : String := include_str "../cert/spectra_after_C.txt"
def concord_after_C : String := include_str "../cert/concord_after_C.txt"
def warrant_after_D : String := include_str "../cert/warrant_after_D.txt"
def caselog_after_D : String := include_str "../cert/caselog_after_D.txt"
def spectra_after_D : String := include_str "../cert/spectra_after_D.txt"
def concord_after_D : String := include_str "../cert/concord_after_D.txt"
def negative_controls : String := include_str "../cert/negative_controls.txt"

end LangStress.Cert
