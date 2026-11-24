import Mathlib.Data.Nat.Pairing
import Mathlib.Algebra.BigOperators.NatAntidiagonal

namespace YM.MS.Dock
open Finset
def shortB (n:ℕ) := (antidiagonal n).filter fun p=> p.1<n ∧ p.2<n
def shortM (n:ℕ) := (antidiagonal n).filter fun p=> p.2<n
end YM.MS.Dock
