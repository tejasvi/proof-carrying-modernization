# The statement of one theorem on a single line: from `theorem NAME` to the `:=` that ends the
# statement (exclusive), whitespace runs collapsed to one space.
# usage: awk -v name=NAME -f sig.awk FILE
$0 ~ ("^theorem " name "( |$)") && !done { on = 1 }
on {
  s = s " " $0
  if ($0 ~ /:=[ \t]*(by)?[ \t]*$/) { on = 0; done = 1 }
}
END {
  sub(/:=[ \t]*(by)?[ \t]*$/, "", s); gsub(/[ \t]+/, " ", s); sub(/^ /, "", s); sub(/ $/, "", s)
  print s
}
