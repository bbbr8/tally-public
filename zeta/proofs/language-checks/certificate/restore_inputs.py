"""Verify the issued Lean sources and restore their certified input files."""

import hashlib
import json
import lzma
from pathlib import Path
import re
import tempfile


def main():
    here = Path(__file__).resolve().parent
    document = (here / "Lean-Certificate.md").read_text(encoding="utf-8")
    sources = re.findall(
        r"^\| (\w+\.lean) \| `([a-f0-9]{64})` \|$", document, re.MULTILINE,
    )
    if not sources or len(dict(sources)) != len(sources):
        raise ValueError("The certificate's Lean source list is empty or contains duplicates.")
    for name, expected in sources:
        data = (here.parent / "LangStress" / name).read_bytes()
        if hashlib.sha256(data).hexdigest() != expected:
            raise ValueError(f"Certificate source SHA-256 mismatch for {name}")
    rows = re.findall(
        r"^\| ([a-zA-Z0-9_]+\.txt) \| [\d,]+ \| `([a-f0-9]{64})` \|$",
        document, re.MULTILINE,
    )
    archive = here / "inputs"
    if not rows or len(dict(rows)) != len(rows):
        raise ValueError("The certificate's input list is empty or contains duplicates.")
    if {name + ".xz" for name, _ in rows} != {p.name for p in archive.glob("*.xz")}:
        raise ValueError("The archived inputs differ from the list in the certificate.")

    destination = here.parent / "cert"
    superseded = json.loads((here / "superseded-inputs.json").read_text(encoding="utf-8"))
    destination.mkdir(exist_ok=True)
    for name, expected in rows:
        target = destination / name
        data = lzma.decompress((archive / (name + ".xz")).read_bytes())
        if hashlib.sha256(data).hexdigest() != expected:
            raise ValueError(f"Certificate SHA-256 mismatch for {name}")
        if target.exists():
            digest = hashlib.sha256(target.read_bytes()).hexdigest()
            if digest == expected:
                continue
            if digest != superseded.get(name):
                raise ValueError(f"Existing {name} differs from the certified input.")
        temp = tempfile.NamedTemporaryFile(dir=destination, delete=False)
        temp_path = Path(temp.name)
        try:
            with temp:
                temp.write(data)
            temp_path.replace(target)
        finally:
            temp_path.unlink(missing_ok=True)
    print(f"Verified {len(sources)} Lean sources and {len(rows)} inputs against the issued certificate.")


if __name__ == "__main__":
    main()
