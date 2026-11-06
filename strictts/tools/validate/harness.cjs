// Node side of a validation driver that calls external functions: the difftest harness
// (tests/difftest/harness.cjs: final status line, trace of the external calls and Date.now()
// values for the Lean run to replay), with Math.random() answering 0 as the `rand` oracle of
// Lean's World.init does.
'use strict';
Math.random = () => 0;
require('../../tests/difftest/harness.cjs');
