import YM.Pier.Lair.Lit

/-! Charge uniform differences of moment values in scaled position, in the chosen moving norm. leading all-r jets needed from master for this. NOT priced coefficients or all fixed-scale differences. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pier.Lair.Present
open Function Filter Set Table Metric Extraction Climb Analysis Ward Spec
open Trace Trace.Over Trace.Terrace Trace.Pilot MergeProof.East Next.Rank
open Next.UVStress Spin
open MeasureTheory SharpGram Lenses
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
   {F:Spec.Final C f S}{n:ℕ}{Y:ℝ→FamilyBasis (C:=C) S} (P:Present F Y)
   (d:Caps n)(s:Set (Points n))(hs:IsCompact s)(hS:s⊆conf n)
set_option quotPrecheck false
local notation "B"=> (Bel C.book)
local notation "C₀"=> (Maxwell.Free.hierarchy C.labels)
include P hs hS
omit P hs hS in
def tagsX (Y:ℝ→FamilyBasis (C:=C) S) (d:Caps n) (r:ℝ) (y: (i: Fin n)→ (Bel C.book).Field (d i)) (x:Points n): ℂ:= S.classMoment S d (r • x) (fun i=>Y r (d i) (y i))
local notation "Kᵣ"=> tagsX Y d
local notation "tᵣ"=> (C₀)
private lemma smoothU (y:Ribbon (Bel C.book) d): ∃ K:ℝ,0<K∧ ∀ᶠ r in Pilot.trail,∀ x∈s, DifferentiableAt ℝ (Kᵣ r y) x∧ ‖fderiv ℝ (Kᵣ r y) x‖≤K:=by
   have he:= P.anyJets F Y (fun _=>y) y (fun _=> tendsto_const_nhds) 1 s hs hS 1 one_pos
   let t:(B).Tag→ Set ℕ:=fun _=>∅; let r(x):=‖fderiv ℝ (disc (hang _ y)) x‖
   have hh : ContinuousOn r s:= fun x hx=> by
       exact ((show ContDiffAt ℝ ∞ (disc (hang _ y)) x from (smoothDisc (C₀).smooth _ x (hS hx)).contDiffAt ((conf_open _).mem_nhds (hS hx))).continuousAt_fderiv (by simp)).norm.continuousWithinAt
   obtain ⟨b,hb⟩:= (hs.image_of_continuousOn hh).bddAbove
   refine ⟨1+max b 1, by positivity,?_⟩
   filter_upwards [self_mem_nhdsWithin (a:=0), he] with i hp hi x hx
   let M(j): S.Tag:= ⟨d j,Y i (d j) (y j)⟩
   have hw : ContDiffAt ℝ ∞ (Kᵣ i y) x:= (smoothZoom F.room.kernel.smooth M (show 0 < i from hp) x (hS hx)).contDiffAt ((conf_open _).mem_nhds (hS hx))
   have ht := hi x hx
   refine ⟨hw.differentiableAt (by simp),?_⟩
   change ‖iteratedFDeriv ℝ 1 (Kᵣ i y) x - iteratedFDeriv ℝ 1 (disc (hang _ y)) x‖≤ _ at ht
   rw [← norm_iteratedFDeriv_one]; refine (norm_le_norm_sub_add _ (iteratedFDeriv ℝ 1 (disc (hang d y)) x)).trans ((add_le_add ht le_rfl).trans ?_); rw [norm_iteratedFDeriv_one (disc (hang d y))]; exact add_le_add le_rfl ((show r x≤ b from hb (mem_image_of_mem _ hx)).trans (le_max_left ..))
section bound
omit P hs hS
local notation "T"=> fun i=> (B).Field (d i)
private lemma budgets (i: Code (T)): ∃ B₀:ℝ,0 ≤ B₀∧∀ (x:Ribbon (Bel C.book) d), ‖coords (T) i x‖ ≤ B₀*∏ j:Fin n, ‖x j‖:=by
   let Z(j:Fin n):= LinearMap.toContinuousLinearMap ((Module.finBasis ℂ ((B).Field (d j))).coord (i j))
   let t:=∏ j: Fin n,‖Z j‖; refine ⟨t,Finset.prod_nonneg (fun i _=> norm_nonneg (Z i)),fun x=>?_⟩
   unfold coords; rw [norm_prod]; unfold t; rw [← Finset.prod_mul_distrib]; exact Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i _=> (Z i).le_opNorm _)
end bound
-- immediate compact Lipschitz in exact positions scaled.
lemma confines : ∃ K c:ℝ,0<K∧0<c∧ ∀ᶠ r in Pilot.trail,∀ x∈s,∀ y:Points n,‖y-x‖≤ c → y∈conf n ∧
    ∀ v : Ribbon (Bel C.book) d, ‖tagsX Y d r v y-tagsX Y d r v x‖ ≤ K*(∏ i,‖v i‖) * ‖y-x‖:=by
   obtain ⟨c,hc,h⟩:= hs.exists_cthickening_subset_open (conf_open _) hS
   let p(i):= (B).Field (d i)
   let X:= Metric.cthickening c s
   have ht (x)(hx:x∈s): closedBall x c ⊆ X:= fun y hy=> mem_cthickening_of_dist_le _ x _ _ hx hy
   choose K hK hx using fun i:Code p=> smoothU P d X (hs.cthickening) h (combination p i)
   choose b hb hU using (budgets d (C:=C))
   let a:=∑ i: Code p,K i*b i; have ha:0 ≤ a:= Finset.sum_nonneg fun i _=>mul_nonneg (hK i).le (hb i)
   refine ⟨a+1,c,by linarith,hc,?_⟩
   filter_upwards[eventually_all.mpr hx] with r hr x hx y hy
   have he: y∈closedBall x c:= mem_closedBall.mpr (by rw [dist_eq_norm]; exact hy)
   refine ⟨h (ht _ hx he),fun w=>?_⟩
   let z(v:Points n):= (S.classMoment S d (r • v)).compLinearMap fun i => (Y r (d i)).toLinearMap
   let J:= ∏ i:Fin n,‖w i‖; have hJ:0 ≤ J:= Finset.prod_nonneg fun _ _=> norm_nonneg _; let u:=‖y-x‖
   have hp(i:Code p): ‖z y (combination p i)-z x (combination p i)‖ ≤ K i*u:=by
       refine Convex.norm_image_sub_le_of_norm_fderiv_le (f:=Kᵣ r (combination p i)) (s:=closedBall x c) (fun z hz=> (hr i z (ht _ hx hz)).1) (fun z hz=> (hr i z (ht _ hx hz)).2) (convex_closedBall _ _) (mem_closedBall_self hc.le) he
   change ‖(z y-z x) w‖ ≤ (a+1)*J*u
   rw [basis_tuple p _ (z y-z x)]
   calc
     _ ≤ ∑ i : Code p, ‖coords p i w*((z y-z x) (combination p i))‖:= norm_sum_le ..
     _ ≤ ∑ i : Code p,(K i*b i)*J*u:= Finset.sum_le_sum fun i _=>by
         rw[norm_mul]; refine (mul_le_mul (hU i w) (hp i) (norm_nonneg _) (mul_nonneg (hb i) hJ)).trans_eq ?_; unfold J; ring
     _ = a*J*u:=by rw[← Finset.sum_mul,← Finset.sum_mul]
     _ ≤ _:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (lt_add_one a).le hJ) (norm_nonneg _)
end YM.Pier.Lair.Present
