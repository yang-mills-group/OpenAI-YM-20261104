import YM.FVA1.Film
/-! Widen the complete test/derivative/label bill *after* the menu calculation.
Require the radius test per **allowed monomial**, not just generators.
-/

noncomputable section
set_option autoImplicit false
namespace YM.FVA1.Film
open MeasureTheory Finset Function Filter Lattice Wilson RG
open Marker Overlay Overlay.GapsLocal Push.GridApprox.Nil MergeProof Accent
open Push Push.AbsoluteSums
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{P:RG.Rep G n}

variable {V T J:Type}[DecidableEq V][AddCommGroup T][Module ℂ T]{Γ:Census V}
variable {D:Film J T Γ P}
variable {C:Controls V T}{w w':V→ℝ}{p a b c k t a' b' c' : ℝ}

lemma Pays.widen (h:D.Pays C w p a b c k) (hw:∀ i,0<w' i)
    (ht:0 ≤ t)(hx:∀ i:Γ.Mode,Poly.toll w' i ≤ t*Poly.toll w i)(ha:t*a ≤ a')(hb:t*b ≤ b')(hc:t*c≤c') :
    D.Pays C w' p a' b' c' k:= by
  obtain ⟨u,hu,hQ,hF⟩:=h.bulk; obtain ⟨v,hv,hV,hK⟩:=h.wind
  have hp {J:Type} (f:J→Sheet Γ)(hf:∀ i,0≤f i)(B:ℕ)(X:J→Support n){a a':ℝ}(hX:Ac.Hit X B (fun i=>wordsPrice w (f i)) p a)(hs:t*a ≤ a'): Ac.Hit X B (fun i=>wordsPrice w' (f i)) p a':=by
    intro i
    refine budget_loosen (budget_mono (budget_scale ht (hX i)) (fun j=>?_) (fun j=>?_)) hs
    · split; next => exact mul_nonneg (sum_words_pos w' hw _ (hf j)) (Real.exp_pos _).le
      next => exact le_rfl
    split
    next=>
       rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
       unfold wordsPrice; rw [Finset.mul_sum]; refine Finset.sum_le_sum fun i _=>?_ ; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (hx _) (hf j i)
    next=>rw [mul_zero]
  have hl(i):w' i ≤ t*w i:=by simpa only [Poly.solo_toll] using hx (Γ.fire i)
  refine ⟨hw,h.marker,h.extraSupport,fun i x hX=> ?_,⟨u,hu,hp _ hu _ _ hQ hb,hF⟩,⟨v,hv,hp _ hv _ _ hV ((mul_assoc ..).symm.trans_le (mul_le_mul_of_nonneg_right hc h.marker.le)),hK⟩⟩
  exact (mul_le_mul_of_nonneg_right (hl i) (norm_nonneg _)).trans (le_trans (mul_assoc ..).le ((mul_le_mul_of_nonneg_left (h.localU i x hX) ht).trans ha))
end YM.FVA1.Film
