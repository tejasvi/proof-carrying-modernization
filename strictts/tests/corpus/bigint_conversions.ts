// @numbers
// BigInt <-> number conversions and BigInt.asIntN/asUintN (number model needed).
console.log(`${BigInt.asIntN(8, 255n)} ${BigInt.asUintN(8, -1n)} ${BigInt.asIntN(64, 2n ** 63n)}`);
console.log(`${BigInt(42)} ${Number(10n ** 15n)} ${BigInt("123456789012345678901234567890")}`);
try { console.log(`${BigInt(1.5)}`); } catch (e) { console.log(`${(e as Error).name}`); }
try { console.log(`${BigInt("12x")}`); } catch (e) { console.log(`${(e as Error).name}`); }
console.log(`${Number(2n ** 53n + 1n)} ${Number(-(2n ** 64n))}`);
