from pathlib import Path

import_path = Path("./Hundred")
root_path = Path("./Hundred/Root.lean")

imports = []

for path in sorted(import_path.glob("*.lean")):
  # Convert e.g. Hundred/p00_comments.lean -> Hundred.p00_comments
  module_name = ".".join(path.with_suffix("").parts)
  if module_name != "Hundred.Root":
    prefix = "-- " if "TODO" in path.name else ""
    imports.append(f"{prefix}import {module_name}")

root_path.write_text("\n".join(imports) + "\n")

print(f"Wrote {len(imports)} imports to {root_path}")