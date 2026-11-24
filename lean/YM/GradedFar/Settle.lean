import YM.GradedFar.Axil
import YM.Integration.WilsonPositionHomogeneousCoefficients
import YM.GradedFar.Era
/-!
# Preparation inclusion and accrual

Cap navigation for the actual frame and its genuine realized exponent through each horizon.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff
namespace Week
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet Neighbor
open YM.Integration.GradedFar.Tariff.Playbill
open YM.Integration.GradedFar.Tariff.Billboard
open WilsonPositionHomogeneousCoefficients
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    (J P:ℝ→tower S) (Z:WilsonPrescription G)
    {t:ℝ→ℝ}{n m d h p:ℕ}
lemma Included_chain (H:∀ d, Included F J d (d+1) (Nat.le_succ _)): Connected F J:=by
 intro h d hp; induction h,hp using Nat.le_induction with
 | base => refine Eventually.of_forall (fun r u=>?_); rw [F.sector.derivatives.arrival F.room.kernel.laws.toSymmetric F.phase.transport.injection]; rfl
 | succ n hm ih => filter_upwards [ih,H n] with r hr hn v; rw [show up (hm.trans (Nat.le_succ n)) v=up (Nat.le_succ n) (up hm v) from rfl,hn,hr, F.sector.derivatives.transit F.room.kernel.laws.toSymmetric F.phase.transport.injection]
lemma Included_turn {d h:ℕ}(hv:d≤h)(hp:Included F J d h hv)
    (f:∀ h:ℕ,ℝ→Change G h)(he:∀ r,∀ v:Sec G d,stand (f h r) (up hv v)= up hv (stand (f d r) v))
    (hC:∀ h,∀ᶠ r in trail, ∀ v:Sec G h, assign P r h v=assign J r h (stand (f h r) v)):
    Included F P d h hv:= by
 filter_upwards [hp,hC d,hC h] with r hr hD ht u; rw [ht,hD,he,hr]

local notation "fᵀ" => attends Z
-- use guide G
private def receipt (a:Toon G h) (v:Sec G h): MoveSpace G h →L[ℝ] ℂ := LinearMap.toContinuousLinearMap {
    toFun p:= coord a (((guide G h).symm p).val v)
    map_add' _ _:=by rw [map_add]; exact map_add (coord a) ..
    map_smul' c p:= by rw [map_smul]; exact map_smul ((coord a).restrictScalars ℝ) ..
}
private lemma turned (a:Toon G h) (v:Sec G h) (p:Change G h): receipt a v (guide G h p)= coord a (p.val v):=by
 change coord a (((guide G h).symm (guide _ _ _)).val v) = _; rw [LinearEquiv.symm_apply_apply]
private lemma letterCost (H:Warrant Z) (i:ℕ)(a:Toon G h)(v:Sec G h): coeff i (attends Z v a)= coord a ((letter Z h i).val v)+if i=0 then coord a v else 0:=by
 rw [attends,coeff_mk]; split_ifs with he
 · subst i; rw [(H.scheme h).scale.zero]; simp [letter]
 rw [positive Z H h he,add_zero]
lemma accrued (H:Warrant Z) (u:ℝ→Change G h)(v:Sec G h)(a:Toon G h) (hx: ∀ q:ℕ,∃ A:ℝ,0 ≤A∧ ∀ᶠ r in trail,
    ‖guide G h (u r)- ∑ i∈Finset.range (q+1), t r^i • guide G h (letter Z h i)‖ ≤ A*|t r|^(q+1)):
    Expansion t trail (fun r=> coord a (stand (u r) v)) (attends Z v a):= by
 refine ⟨fun i=>FVA2.GradedFar.Cart.Charge.const _,fun p=>?_⟩
 obtain ⟨A,hA,hp⟩:= hx p; let u':=receipt a v; let v' (i):= coord a ((letter Z h i).val v)
 refine ⟨ ‖u'‖*A, by positivity,?_⟩; filter_upwards [hp] with r hr i
 have h₁ (f:Finset ℕ): u' (∑ j∈f, t r^j • guide G h (letter Z h j))= ∑ j∈f, (t r:ℂ)^j*v' j:=by
    unfold u' v'; simp_rw [map_sum,map_smul,turned, Complex.real_smul,Complex.ofReal_pow]
 have he : appointedH140Crop p (t r) (attends Z v a)=(∑ j∈Finset.range (p+1),(t r:ℂ)^j*v' j)+coord a v:= by
    simp_rw [crop_eq, letterCost Z H,mul_add]; rw [Finset.sum_add_distrib]; apply congrArg
    rw [Finset.sum_eq_single 0] <;> simp; aesop
 rw [stood,map_add,he]; have h₂ := (u'.le_opNorm _).trans (mul_le_mul_of_nonneg_left hr (norm_nonneg (u')))
 rw [map_sub,h₁, ← mul_assoc] at h₂; unfold u' at h₂; rw [turned] at h₂; exact le_trans (le_of_eq (congrArg norm (by abel))) h₂
lemma accrual (H:Warrant Z) (u:ℝ→Change G h) (hs:∀ᶠ r in trail,∀ v:Sec G h, assign P r h v= assign J r h (stand (u r) v))
    (hx: ∀ q:ℕ,∃ A:ℝ,0 ≤A∧ ∀ᶠ r in trail,
    ‖guide G h (u r)- ∑ i∈Finset.range (q+1), t r^i • guide G h (letter Z h i)‖ ≤ A*|t r|^(q+1)) : widens J P Z h t:=by
 intro i v; refine Receives.congr (accrued Z H u v i hx) ?_ (fun j=>rfl)
 filter_upwards [hs] with r hr; funext x
 change coord i (stand (u r) v) = coord i ((assign J r h).symm (assign P r h v)); rw [hr,LinearEquiv.symm_apply_apply]
end Week
end YM.Integration.GradedFar.Tariff
