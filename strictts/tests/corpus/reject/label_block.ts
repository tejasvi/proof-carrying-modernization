// @reject no-label-non-loop
blk: {
  console.log("a");
  break blk;
}
