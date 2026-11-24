import YangMills.WilsonProof.NativeSupport.OriginalGrowth
import YM.FullVolume.Nectar.LiegeR
import Mathlib.Data.Nat.Log

/-! Multiply the linear tariffs on the actual schedule. The accumulated
loss is a power of its total block scale. The quadratic and newborn
expenses form an additive error on that same full inlet. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Filter Finset Lattice Wilson RG RGComparison.Core16 PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge}

def tariffDegree (price : ℝ) := Nat.clog 3 ⌈256*(1+|price|)⌉₊+1

theorem original_tempo {q:ℝ} (Θ : Luna.Tableau q 300) (L:Side) (large:3 ≤ L.val) {κ:ℝ} (stain:κ ≤ 1) :
    16*(Luna.Frets.tempo Θ L+κ) ≤ (L.val:ℝ)^tariffDegree Θ.price := by
  let a:=256*(1+|Θ.price|)
  let k:=Nat.clog 3 ⌈a⌉₊
  have l3 : (3:ℝ) ≤ L.val := by exact_mod_cast large
  have powCap : a ≤ (L.val:ℝ)^k := by
    apply (Nat.le_ceil _).trans
    exact_mod_cast (Nat.le_pow_clog (by decide : 1 < 3) ⌈a⌉₊).trans (Nat.pow_le_pow_left large k)
  change 16*((Θ.price*(1+(L.val:ℝ))+1)*2+κ) ≤ (L.val:ℝ)^(k+1)
  rw [pow_succ]
  apply le_trans _ (mul_le_mul_of_nonneg_right powCap (Nat.cast_nonneg _))
  dsimp [a]
  have hθ := mul_le_mul_of_nonneg_right (le_abs_self Θ.price) (by positivity : 0 ≤ 1+(L.val:ℝ))
  nlinarith only [hθ,stain,l3,abs_nonneg Θ.price, mul_nonneg (abs_nonneg Θ.price) (sub_nonneg.mpr l3)]

end YM.Integration.InletSusceptibility.Packet
