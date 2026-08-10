#!/usr/bin/env python3

from pathlib import Path
import re


PREFIX_RE = re.compile(r"^[^_]+")

def rename_lean_files(directory) -> None:
  directory = Path(directory)

  # Find all .lean files and sort alphabetically by their original filename.
  files = sorted(
    (path
      for path
      in directory.glob("*.lean")
      if path.name != "Root.lean"),
    key=lambda path: path.name,
  )

  if len(files) >= 100:
    raise ValueError("This script supports fewer than 100 .lean files.")

  # Build a mapping from each original prefix to its new prefix.
  renames = {}

  for number, path in enumerate(files):
    match = PREFIX_RE.match(path.stem)
    if not match:
      raise ValueError(f"Could not determine prefix for {path.name}")

    old_prefix = match.group(0)
    new_prefix = f"p{number:02d}"

    if old_prefix in renames:
      raise ValueError(
        f"Duplicate prefix {old_prefix!r} found."
      )

    renames[old_prefix] = new_prefix

  # Build one regex matching any original prefix.
  old_prefix_pattern = "|".join(
    re.escape(prefix)
    for prefix in sorted(renames, key=len, reverse=True)
  )

  import_pattern = re.compile(
    rf"(?<=\.)({old_prefix_pattern})(?=_)"
  )

  # Replace imports using the original text only.
  def replace_import_prefix(match: re.Match[str]) -> str:
    old_prefix = match.group(1)
    return renames[old_prefix]

  for path in files:
    text = path.read_text(encoding="utf-8")

    text = import_pattern.sub(
      replace_import_prefix,
      text,
    )

    path.write_text(text, encoding="utf-8")

  # Rename files.
  for old_path in files:
    old_prefix = PREFIX_RE.match(old_path.stem).group(0)
    new_prefix = renames[old_prefix]

    new_name = old_path.name.replace(
      old_prefix,
      new_prefix,
      1,
    )

    new_path = directory / new_name

    if new_path != old_path:
      old_path.rename(new_path)

  print("Renaming complete.")


if __name__ == "__main__":
  rename_lean_files("./Hundred")