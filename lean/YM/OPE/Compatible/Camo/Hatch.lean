import YM.OPE.Compatible.Munch.Porch
import YM.OPE.Compatible.Munch.Rind
import YM.OPE.Compatible.Camo.Crow
/-! # outward telesc bills on varying loop allowance. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
open PertExtension Series Libra GaussianScore Stranded Radial Jargon Cinders Score Lav Limn
variable {I:Type}{v:ℝ}
variable (G:Gauge)(s c u C β:ℝ)(k:ℕ)
abbrev wealthV (β v:ℝ):= 1+‖v+4*β‖
private lemma spell (a b v x y z:ℝ): ‖a‖+(‖b‖+‖v*x‖)+‖y‖+‖z‖ ≤ (1+‖v‖)*(‖a‖+(‖b‖+‖x‖)+‖y‖+‖z‖):=by
        rw[norm_mul]; nlinarith only [norm_nonneg x,mul_nonneg (norm_nonneg v) (show 0≤‖a‖+‖b‖+‖y‖+‖z‖ by positivity)]
lemma w45F : ∃ (D:ℝ)(n:ℕ),0≤D ∧∀ (v t z a:ℝ), ‖wallet3 G k s c v u C t z a β‖ ≤ wealthV β v*D*(1+(‖t‖+(‖z‖+‖a‖)))^n:=by
       obtain ⟨D,n,hD,H⟩:=w45 G s c (1-4*β) u C β k; refine ⟨D,n,hD,fun v t z a=>?_⟩; let p:=fun v=> wallet3 G k s c v u C t z a β; let W:=v+4*β; rw[mul_assoc (wealthV β v)]; refine le_trans ?_ (mul_le_mul_of_nonneg_left ((Real.le_norm_self (p (1-4*β))).trans (H _ _ _)) (by unfold wealthV; positivity)); unfold p wallet3; rw [Real.norm_of_nonneg (add_nonneg (add_nonneg (add_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))) (norm_nonneg _)) (norm_nonneg _)),sub_add_cancel]; let P:=fun w=> price2 G k 2 s c u C t z a w; rw [show price2 G k 2 s c u C t z a (v+4*β)=W* P 1 from (by unfold P W price2;ring)]; exact spell .. -- shape
lemma wC : ∃ (D:ℝ)(n:ℕ),0≤D∧ ∀ (v J z a t:ℝ), Caver G k s c v u C t z a J β ≤ wealthV β v*D*(1+(‖J‖+‖z‖+‖a‖))^n*(1+‖t‖)^n:=by
       obtain ⟨D,n,hD,H⟩:= offered_W G s c (1-4*β) u C β k; refine ⟨D,n,hD,fun v J z a t=>?_⟩; rw[mul_assoc (wealthV β v),mul_assoc (wealthV β v)]; refine le_trans ?_ (mul_le_mul_of_nonneg_left (H J z a t) (by unfold wealthV; positivity)); let W:=v+4*β; unfold Caver; rw [sub_add_cancel]; let P:= fun w=> Cave2 G k 2 s c u C t z a J w; rw [show Cave2 G k 2 s c u C t z a J (v+4*β)=W*P 1 from (by unfold P W Cave2;ring)]; exact spell ..
end YM.OPE.Borealis.Galea
