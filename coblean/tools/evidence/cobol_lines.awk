# Non-comment lines of a fixed-format COBOL source: lines whose indicator (column 7) is not
# '*' or '/' and whose program text (columns 8-72) is not blank (a '-' continuation counts).
# usage: awk -f cobol_lines.awk FILE...   (prints the total)
{ l = $0; sub(/\r$/, "", l)
  if (length(l) >= 7 && (substr(l, 7, 1) == "*" || substr(l, 7, 1) == "/")) next
  t = substr(l, 8, 65); gsub(/[ \t]/, "", t)
  if (t == "" && substr(l, 7, 1) != "-") next
  n++ }
END { print n + 0 }
