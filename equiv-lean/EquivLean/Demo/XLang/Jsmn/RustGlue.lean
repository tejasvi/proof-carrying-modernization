import EquivLean.Demo.XLang.Jsmn.Equiv
import EquivLean.Demo.XLang.Jsmn.RustMain

/-!
# jsmn: the Rust side's theorem as `RSpec`

`Rust.rust_spec` (`RustMain`) is the plumbing's `RSpec` (`Equiv`) as stated: for every input whose
text is shorter than `2^28` bytes, the Rust run returns normally with the model's observation.
-/

namespace EquivLean.Demo.XLang.Jsmn

theorem rust_rspec : RSpec := Rust.rust_spec

end EquivLean.Demo.XLang.Jsmn
