import YM.Integration.WilsonMarkedUltravioletMixedWallet

/-! Spend the original output radius once, on all held fields and physical
modes in the same majorant. No sum of separate suprema is required. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedUnweight
open Finset Function Lattice Wilson RG Marker Push AbsoluteSums Extra.Histories Ac MergeProof MergeProof.Accent
open GridApprox.Nil
open scoped BigOperators Classical

theorem original {G:Gauge} {n:Side} {I V:Type} [Fintype I] [DecidableEq V] {J:Census V}
    {S:I→Support n} {F:I→Config G n→Poly J} {B:ℕ} {α δ ε:ℝ} {w:V→ℝ}
    (bank:Towed w S F B α δ) (wd:∀v,0<w v) (dp:0<δ) (en:0≤ε)
    (fee:∀i U s,(F i U).part s≠0→δ≤ε*Poly.toll w s) :
    Towed (fun _:V=>(1:ℝ)) S F B α ε := by
  have paid : ∀i U s,(F i U).part s≠0→1≤(ε/δ)*Poly.toll w s := by
    intro i U s hit
    rw [div_mul_eq_mul_div,le_div_iff₀ dp,one_mul]
    exact fee i U s hit
  have funded:=WilsonMarkedUltravioletMixedWallet.purchase bank wd (σ:=0) le_rfl
    (div_nonneg en dp.le) paid (D:=0) (fun _ _ _ _=>Nat.zero_le _)
  simpa only [sub_zero,neg_zero,zero_mul,Real.exp_zero,mul_one,div_mul_cancel₀ _ dp.ne'] using funded

end YM.Integration.WilsonMixedTaggedUnweight
