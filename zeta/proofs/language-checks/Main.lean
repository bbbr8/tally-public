import LangStress
open LangStress

/-- Report disagreements. In check mode, require at least one case and agreement on every case. -/
def main (args : List String) : IO UInt32 := do
  let (checkMode, path) ← match args with
    | [] => pure (false, "cases.txt")
    | ["--check", path] => pure (true, path)
    | [path] =>
      if path == "--check" then
        IO.eprintln "usage: oracle [--check] FILE"
        return 2
      pure (false, path)
    | _ =>
      IO.eprintln "usage: oracle [--check] FILE"
      return 2
  let text ← IO.FS.readFile path
  let mut n := 0
  let mut nbad := 0
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.isEmpty then continue
    let (_, bad) :=
      if line.startsWith "W " then Warrant.check line
      else if line.startsWith "C " then CaseLog.check line
      else if line.startsWith "K " then Concord.check line
      else if line.startsWith "S " then Spectra.check line
      else ("?", [s!"UNKNOWN_LINE {line.take 20}"])
    n := n + 1
    if !bad.isEmpty then nbad := nbad + 1
    for b in bad do IO.println b
  IO.println s!"SUMMARY cases={n} disagreeing_cases={nbad}"
  return if checkMode && (n == 0 || nbad != 0) then 1 else 0
