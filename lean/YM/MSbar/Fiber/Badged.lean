import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Pint
import YM.MSbar.Fiber.Sofa

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Fibre S R)(X:Coat T F)(H:Cash W x μ L Q o C T R) (a' : ℝ) (u:ConnectedActivityE6.Alphabet c f→ℝ)
    {q A B b e a χ' v d:ℝ}{j n:ℕ}{χ:Chi} (Ξ : Utopia H j v d r q χ)
open Itinerary Animals
variable {Y t u v:ℝ}{N : March.Captain H j q d v Y A b r B t n χ}(h : Herd H N.conduit A B n)
open Greenbelt March Next.Foundations


-- for every marked nonzero occurrence. `paper` is not the insertion read;
-- it just carries the numbers and the ticket and has a full gauge action.
def paper (M:Fibre S R):Leaf R:=⟨M.turn,0,(fun _ _ _ _=>rfl),fun _ h=>(h rfl).elim,M.blank,M.weight,fun v=>by change ‖(0:ℝ)‖ ≤ _;rw [norm_zero]; exact M.profit,(fun _ _=>rfl),measurable_const⟩
local notation "l₀" => M.lotus T x χ o.K W o.a Q.table Q.halo
include H
lemma petalsF (V:Config G c)(i m n:ℕ)(ht : i ≤ p.card-1)(hm: n ≤ Cash.numP p) : |l₀ V p| * (1+H.shapeW p)^m ≤ (jewelDebt (paper M) Q L x)*persona (paper M) H C H.opt i m n p:=by
  have h₀:0 ≤ persona (paper M) H C H.opt i m n p:= earned (paper M) H C H.opt H.positive ..
  let I:= (Fintype.card (Greenbelt.Reserve S):ℝ); letI: Nonempty (Forest S.ratio):= Tree.select S.ratio S.patch.odd_side
  have hi:0<I:=by unfold I; positivity
  let F r:=prism T x χ o.K V (allot r)
  let b r:= M.bloom (F r) W o.a Q.table Q.halo p
  have he r: ‖b r‖ * (1+H.shapeW p)^m ≤ (jewelDebt (paper M) Q L x)*persona (paper M) H C H.opt i m n p:=by
    unfold b Fibre.bloom; split
    next ha=>
      by_cases hp:M.turn.badge S∈p
      swap; · unfold Fibre.steep likely; simp_rw [M.tithe_off _ _ p hp,Finset.sum_const_zero,mul_zero,norm_zero,zero_mul]; exact mul_nonneg (dew (paper M) H|>.2.1) h₀
      have hR : H.ticketsP i n 0 p := ⟨ha.1,ht,hm,H.positive_volume p⟩
      let Q0:=∏ i∈p.erase (M.turn.badge S), H.text i; let c:=M.weight * Q0; let A:=planted (F r) p
      have hs (i): ‖M.tithe (A.taggedL i) (own p) W o.a Q.table Q.halo p‖ ≤ c:=
        (norm_integral_le_integral_norm _).trans (by have hx:=(M.tip (A.taggedL i) (own p) H rfl (planted_valid (F r) p) p).2.2; rw [if_pos hp] at hx; exact hx)
      have hv : ‖M.steep A (own p) W o.a Q.table Q.halo p‖≤c:=by
        unfold Fibre.steep likely
        let v:=(Fintype.card S.Choices:ℝ); have h:0<v:=by unfold v; positivity
        rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr h.le)]
        apply le_trans (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum fun i _=> hs i)) (inv_nonneg.mpr h.le))
        rw [sum_const,nsmul_eq_mul, card_univ, inv_mul_cancel_left₀ h.ne']
      unfold persona; rw [if_pos ⟨hR,hp⟩]; refine (mul_le_mul_of_nonneg_right hv (pow_nonneg (add_nonneg zero_le_one (H.positive_volume p)) _)).trans_eq ?_
      rw [← mul_prod_erase _ _ hp,show needle (paper M) H C _ (M.turn.badge S)=_ from nose (paper M) ..,← mul_assoc (jewelDebt ..), ← mul_assoc (jewelDebt ..),← (dew (paper M) H).2.2]
      unfold c Q0; exact congr_arg (fun z=> M.weight*z*((1+H.shapeW p)^m)) (prod_congr rfl fun j hj=> (sleeve (paper M) H C H.opt j (ne_of_mem_erase hj)).symm)
    next h=> rw [norm_zero,zero_mul];exact mul_nonneg (dew (paper M) H|>.2.1) h₀
  let g:=(1+H.shapeW p)^m; have hh :0≤g:=pow_nonneg (add_nonneg zero_le_one (H.positive_volume p)) _
  change ‖I⁻¹ * ∑ i, b i‖*g≤_; rw [norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr hi.le),mul_assoc]
  apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (norm_sum_le ..) hh) (inv_nonneg.mpr hi.le))
  rw [Finset.sum_mul]; refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _=> he i) (inv_nonneg.mpr hi.le)).trans_eq ?_; rw [sum_const,nsmul_eq_mul,card_univ,inv_mul_cancel_left₀ hi.ne']
lemma whitherF (V:Config G c)(hp:l₀ V p≠0) :
    Ac.Spark H.supportP p ∧ troupe T R Q.halo (radiusB x) p ∧ M.turn.badge S∈p ∧ enlargement S.ratio Q.halo (radiusB x) (RG.inspected M.crest) ⊆ H.unionP p ∧
    (roster p).flags= RG.flags (Pressure.temp x) V∩ H.unionP p ∧ (H.unionP p).Nonempty:=by
  let X r:=prism T x χ o.K V (allot r); let b (r:Greenbelt.Reserve S):= M.bloom (X r) W o.a Q.table Q.halo p
  obtain ⟨z,hz⟩:∃ z,b z≠0:=by by_contra! he; apply hp; change _* ∑ i, b i=0; simp_rw [he,Finset.sum_const_zero, mul_zero]
  have hF : M.turn.badge S∈p:=by by_contra hn; exact hz (M.bloom_off (X z) p hn)
  unfold b Fibre.bloom at hz; split at hz; swap; · exact (hz rfl).elim
  next he=>
  have hx : enlargement S.ratio Q.halo (radiusB x) (RG.inspected M.crest) ⊆ H.unionP p:=by rw [show enlargement _ _ _ _= areas R T Q.halo (radiusB x) (M.turn.badge S) from (M.turn.badge_area ..).symm]; exact subset_biUnion_of_mem _ hF
  refine ⟨he.1,he.2.1,hF,hx,he.2.2.symm,Finset.Nonempty.mono hx ((Finset.Nonempty.image (f:=S.ratio.parent) ?_).mono (halo_subset _ _))⟩
  suffices H : M.crest.Nonempty from H.mono Finset.subset_union_left
  unfold Fibre.crest; cases M.turn
  · exact ⟨_,(R.activities.reg _).anchor⟩
  exact ((R.activities.forced _).inventory_ne).mono (R.activities.forced _).inventory_sup
end YM.PhysicalNext.Repeat.Daisy
