import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Lp.PiLp
/-! Fixed number, rank square meters with pricing relative to stencil,
 EVEN when raw label lower fails at cheap uniform prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Module Matrix
open scoped BigOperators Topology Classical Matrix
variable {ι X : Type*} [Fintype ι] (E:X→ (ι→ℂ) →ₗ[ℂ] ℂ)
set_option quotPrecheck false
local notation "q"=> (ι→ℂ)
private def deck (x:X) (j:ι):= E x (Pi.single j 1)
private def decks (x:ι→X) : Matrix ι ι ℂ := fun i=>deck E (x i)
private lemma deck_tar (x:X)(v:q): E x v= dotProduct (deck E x) v:=by
    have hv: v=∑ i:ι, v i • Pi.single i 1:=by ext1 i; simp [Pi.single_apply]
    conv_lhs=> rw [hv,map_sum]
    simp only [map_smul,smul_eq_mul]; apply Finset.sum_congr rfl; intro j _; exact mul_comm ..
private lemma deck_fills (hr:∀ v, (∀ x:X,E x v = 0) → v=0): ∃ y:ι→X,(decks E y).det≠0:=by
    let S:=Set.range E
    let Q:=Submodule.span ℂ S
    have h:Q.dualCoannihilator=⊥:=bot_unique (fun v hv=> hr v fun x=> (Submodule.mem_dualCoannihilator v).mp hv _ (Submodule.subset_span (Set.mem_range_self _)))
    have he:Q=⊤:=by rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W:=Q), h,Submodule.dualAnnihilator_bot]
    obtain ⟨b,hB,hV,hN⟩:= exists_linearIndependent ℂ S; let B:= Basis.mk hN (by rw [Subtype.range_coe]; exact (hV.trans he).ge)
    letI K : Fintype b:= FiniteDimensional.fintypeBasisIndex B
    let D: b≃ι:= Fintype.equivOfCardEq (by rw [← finrank_eq_card_basis B, ← finrank_fintype_fun_eq_card ℂ]; exact Subspace.dual_finrank_eq)
    choose y hy using fun i:ι=> hB (D.symm i|>.property)
    refine ⟨y,fun H=>?_⟩
    obtain ⟨v,hv,H'⟩:=exists_mulVec_eq_zero_iff.mpr H; have ht(i):E (y i) v= 0:= (deck_tar E ..).trans (congr_fun H' i)
    have hy': b = Set.range (E∘ y):= by
          ext x; constructor
          · intro hx; exact ⟨D ⟨x,hx⟩, (hy (D ⟨x,hx⟩)).trans (by rw [Equiv.symm_apply_apply])⟩
          rintro ⟨z,rfl⟩; rw [Function.comp_apply,hy]; exact (D.symm z).property
    have hf: v ∈ (Q.dualCoannihilator):=by
           change v∈ ((Submodule.span ℂ S).dualCoannihilator:Set q)
           rw [← hV,Submodule.coe_dualCoannihilator_span]; rintro f hx; obtain ⟨x,rfl⟩:= (show f ∈ Set.range (E∘y) from hy' ▸ hx); exact ht x
    exact hv (show v∈(⊥:Submodule ℂ q) from h ▸ hf)
private lemma modest (h:∀ v,∃ B:ℝ,∀ x:X, ‖E x v‖≤ B): BddAbove (Set.range (fun x=> ‖(decks E x).det‖)):=by
    choose B hB using fun j:ι=> h (Pi.single j 1)
    let T:Set (Matrix ι ι ℂ):= {M|∀ i j, M i j∈ Metric.closedBall 0 (B j)}
    have ht:IsCompact T:= isCompact_pi_infinite (fun i=> isCompact_pi_infinite fun j=> isCompact_closedBall ..)
    apply BddAbove.mono _ (ht.image ((continuous_id (X:=Matrix ι ι ℂ)).matrix_det.norm)).bddAbove
    rintro a ⟨x,rfl⟩; exact ⟨decks E x, fun i j=> Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hB _ _), rfl⟩

lemma voll (hr:∀ v, (∀ x:X,E x v = 0) → v=0) (h:∀ v,∃ B:ℝ,∀ x:X, ‖E x v‖≤ B) :∃ (x:ι→X)(S:q≃ₗ[ℂ]q), (∀ v i,S v i= E (x i) v) ∧ ∀ v:q, ∀ B:ℝ, (∀ i, ‖E (x i) v‖≤ B)→ ∀ y:X, ‖E y v‖≤ 2*(Fintype.card ι)*B :=by
    obtain ⟨y,hy⟩:=deck_fills E hr
    let L(x):= ‖(decks E x).det‖; let U:=Set.range L; have hb:BddAbove U:= modest E h
    have hu(x): L x ≤ sSup U:= le_csSup hb ⟨x,rfl⟩
    have hf:0<sSup U:= lt_of_lt_of_le (norm_pos_iff.mpr hy) (hu y)
    obtain ⟨r,⟨x,rfl⟩,hr⟩:=(lt_csSup_iff hb ⟨_,⟨y,rfl⟩⟩).mp (half_lt_self hf)
    let A:=decks E x; have hX:0<‖A.det‖:= (half_pos hf).trans hr; have h':A.det≠0:= norm_pos_iff.mp hX
    let α:=LinearMap.pi (E∘ x); have hi(v):A *ᵥ v=α v:=funext fun j=> (deck_tar E (x j) ..).symm
    have hR:Surjective α:=by
       intro w; refine ⟨A.det⁻¹ • A.cramer w,?_⟩; rw [← hi,mulVec_smul,mulVec_cramer,inv_smul_smul₀ h']
    refine ⟨x,LinearEquiv.ofBijective α ⟨Module.End.injective_of_surjective ℂ _ hR,hR⟩,fun _ _=>rfl,?_⟩
    intro v B hv y
    let u:=deck E y; let c:= Aᵀ.cramer u; have hc(i): ‖c i‖≤2*‖A.det‖:=by
           have hx:A.updateRow i u = decks E (Function.update x i y):=by ext i' j; by_cases h:i'=i<;> simp [h,Matrix.updateRow_apply,A,decks,u]
           unfold c; rw [cramer_transpose_apply, hx]; refine (hu (Function.update x i y)).trans ?_; change _ ≤ 2*L x; linarith only [hr]
    apply le_of_mul_le_mul_left _ hX
    have he : A.det * (E y v)=c ⬝ᵥ A *ᵥ v:=by rw [dotProduct_mulVec, ← mulVec_transpose, show Aᵀ *ᵥ c=_ from mulVec_cramer Aᵀ u,det_transpose,smul_dotProduct,deck_tar]; rfl
    rw [← norm_mul,he,dotProduct]; refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _=>2*‖A.det‖*B) (fun i _=>?_)).trans_eq ?_)
    · rw [hi,norm_mul]; exact mul_le_mul (hc i) (hv i) (norm_nonneg _) (by positivity)
    simp; ring
end YM.RG17
