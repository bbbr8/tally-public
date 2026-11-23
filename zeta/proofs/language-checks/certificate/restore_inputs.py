"""Restore the generated Lean inputs and verify them against the issued certificate."""

import hashlib
import lzma
from pathlib import Path
import re
import tempfile


def main():
    here = Path(__file__).resolve().parent
    document = (here / "Lean-Certificate.md").read_text(encoding="utf-8")
    rows = re.findall(
        r"^\| ([a-zA-Z0-9_]+\.txt) \| [\d,]+ \| `([a-f0-9]{64})` \|$",
        document, re.MULTILINE,
    )
    archive = here / "inputs"
    if not rows or {name + ".xz" for name, _ in rows} != {p.name for p in archive.glob("*.xz")}:
        raise ValueError("The archived inputs differ from the list in the certificate.")

    destination = here.parent / "cert"
    destination.mkdir(exist_ok=True)
    for name, expected in rows:
        target = destination / name
        data = lzma.decompress((archive / (name + ".xz")).read_bytes())
        if hashlib.sha256(data).hexdigest() != expected:
            raise ValueError(f"Certificate SHA-256 mismatch for {name}")
        if target.exists():
            if target.read_bytes() != data:
                raise ValueError(f"Existing {name} differs from the certified input.")
            continue
        temp = tempfile.NamedTemporaryFile(dir=destination, delete=False)
        temp_path = Path(temp.name)
        try:
            with temp:
                temp.write(data)
            temp_path.replace(target)
        finally:
            temp_path.unlink(missing_ok=True)
    print(f"Verified {len(rows)} inputs against the Lean certificate.")


if __name__ == "__main__":
    main()
