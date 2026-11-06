import Testing.ContainsEx
import StrictTS.Testing
open StrictTS StrictTS.Testing ContainsEx

-- Finds an input on which the two versions differ (a NaN search key).
#eval IO.println ((diffCheck Impl.host program hasIndexOfRef hasIncludesRef 3000).getD "no difference found")
-- Also not equivalent: -0.
#eval IO.println ((diffCheck Impl.host program absARef absBRef 3000).getD "no difference found")
