import YM.Frontier6.Bouquet.Market.Pop

/-! Applying the partition machine to full-normal annular tests -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Audit Submodule Fareway
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {P:Ensemble}(i:P){B B' r:ℝ} {g: Full (normal i.val)} {f:Full (fiber P)}

def Flare (f: Full (fiber P))(r:ℝ):Prop:= tsupport f ⊆ cylindrical (fiber P) (normal i.val) (Ringed (normal i.val) r)
lemma Flare.wind (hr:0<r)(he:Flare i f r){x:fiber P}(h:x∈ tsupport f): r⁻¹ • rune i x ∈ Ringed (normal i.val) 1:=by
   change _ ≤ _ ∧ _≤ _; rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr).le,← div_eq_inv_mul]; have hx:rune i x∈ Ringed _ r:= he h; exact ⟨(le_div_iff₀ hr).mpr (le_trans (by ring_nf; exact le_of_eq (by ring)) hx.1), (div_le_iff₀ hr).mpr (by simpa using hx.2)⟩ -- change explicit?
def issued (g:Full (normal i.val))(r:ℝ): Full (fiber P)→ₗ[ℂ] Full (fiber P):= paneM (stretch r g) (stretch r g).contDiff
lemma issued_at (hr:0<r)(x:fiber P) : issued i g r f x=g (r⁻¹ • rune i x)*f x:=by
   change (stretch r g) (rune i x)*f x=_; rw [stretch_eval hr]
lemma issued_support : tsupport (issued i g r f)⊆tsupport f:= screen_subset _ ((stretch r g).contDiff.comp (floorOf (normal i.val) (fiber P)).contDiff) f
lemma Court.issued_here (Z:Court i)(hr:0<r)(he:tsupport g⊆Z.chamber): Z.Contains r (issued i g r f):=by
   let F(x:fiber P):= r⁻¹ • rune i x; have hX:Continuous F:=(by unfold F; fun_prop); intro x hx
   let f' := g ∘ F; refine he (show F x∈ tsupport g from tsupport_comp_subset_preimage g hX ?_); apply tsupport_mul_subset_left (g:=f) (f:=f'); change x∈tsupport (f'*(f:fiber P→ℂ)); rwa [show f'*(f:fiber P→ℂ)=(issued i g r f:fiber P→ℂ) from (funext fun _=> (issued_at i hr _).symm)]
lemma issues (g:Full (normal i.val))(n:ℕ): ∃ C:ℝ,0 ≤ C∧ ∀ (A B:ℝ)(r:P→ℝ)(X:Aura P)(f:Full (fiber P)),0<r i→ Fellow P r X B f (n+n) A → Fellow P r X B (issued i g (r i) f) n (C*A):=by
   obtain ⟨D,hD⟩:= exists_charge n g 1 zero_le_one; have hk:= hD.nonneg; refine ⟨2^n*D,by positivity,fun A B r X f h he=>?_⟩;
   have hp: Charge n (r i) (stretch (r i) g) D:=by simpa only [mul_one] using Charge.stretches h hD
   exact ⟨he.fair.narrower (issued_support i),fun p=>Set.Subset.trans (issued_support i) (he.local_ p), Checks.pane_global i r (stretch (r i) g).contDiff hp (he.local_ i) h he.costs ⟩
lemma cartoons {V:Type*}[Fintype V](g:V→ Full (normal i.val))(ht:∀ x∈ Ringed (normal i.val) 1, ∑ j: V,g j x=1)(hw:Flare i f r)(hr:0<r): f=∑ v:V, issued i (g v) r f:=by
   ext1 x; rw [_root_.sum_apply]; simp_rw [issued_at i hr]; rw [← Finset.sum_mul]; by_cases hp:x∈tsupport f; rw [ht _ (hw.wind i hr hp),one_mul]; rw [image_eq_zero_of_notMem_tsupport hp,mul_zero]
end YM.Frontier6.Bouquet.Atelier
