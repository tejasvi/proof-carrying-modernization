# Lean lines that are neither blank nor comments: `--` lines and `/- ... -/` blocks (doc
# comments included) are left out.
# usage: awk -f lean_lines.awk FILE...   (prints the total)
/^[ \t]*$/ { next }
inc { if ($0 ~ /-\//) inc = 0; next }
/^[ \t]*--/ { next }
/^[ \t]*\/-/ { if ($0 !~ /-\//) inc = 1; next }
{ n++ }
END { print n + 0 }
