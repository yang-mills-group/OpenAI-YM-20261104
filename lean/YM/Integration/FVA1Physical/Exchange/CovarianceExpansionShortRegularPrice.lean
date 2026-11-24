import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionRestoredSingletonPrice
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionFundedAnnulus

/-! The true regular singleton can be cropped on its original torus by the
native support size. Its omitted signed, masked sum has an exponential bound. -/
set_option autoImplicit false
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Function Finset Set MeasureTheory Lattice RG YM.Wilson Marker QuadraticLocal Ac
open Push.AbsoluteSums Push.AbsoluteSums.Animals
open scoped Classical BigOperators
section Stock
variable {G:Gauge}{n:Side}{I T ι:Type*}[DecidableEq I]{J:Census I}
  {B:BudgetPoint}{o:I→Site n}{w:I→ℝ}{a cash:ℝ}

-- Rooted row budget from the accepted CP5RootedRegular file.
private theorem lamp_budget (L:Lamps T ι G B o J) (paid:L.Paid w B.B a cash)
    (positive:∀j,0<w j) (mode:J.Mode) {mark:I} (hmark:mark∈mode.val)
    (tests:ι→T) (fields : ι → Config G n) :
    SumBudget (fun i=>Poly.toll w mode*‖(L.frame i (tests i) (fields i)).part mode‖*
      Real.exp (a*coverNumber B.B (L.ground i))) cash := by
  obtain ⟨f,pos,cost,hit⟩:=paid.budget
  apply budget_mono (hit (o mark))
  · intro i
    exact mul_nonneg (mul_nonneg (Poly.worth positive _).le (norm_nonneg _)) (Real.exp_pos _).le
  · intro i
    change _ ≤ if o mark∈L.ground i then _ else 0
    rw [Lamps.frame,Poly.part_send]
    by_cases id:mode=L.mode i
    · have whereFrom : o mark∈L.ground i := L.roots i mark (id ▸ hmark)
      rw [if_pos id,if_pos whereFrom,id]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (L.light_size i (tests i) (fields i) (cost i (tests i) _ (L.address i).anchor)) (Poly.worth positive _).le) (Real.exp_pos _).le
    rw [if_neg id,norm_zero,mul_zero,zero_mul]
    split
    · exact mul_nonneg (mul_nonneg (Poly.worth positive _).le (pos _)) (Real.exp_pos _).le
    exact le_rfl


end Stock
variable {G:Gauge}{n:Side}{V T ι:Type}[DecidableEq V]{C:Census V}
  {o:V→Site n}{p:BudgetPoint}(L:Lamps T ι G p o C)

private theorem lit_regular (t:T)(i:ι):
    GaugeInvariant (L.light t i) ∧ Measurable (L.light t i) ∧
    UsesFinal p.threshold (L.ground i) (L.light t i):=by
  let E:=L
  have l:=E.legal t i
  change GaugeInvariant (E.light t i) ∧ Measurable (E.light t i) ∧ UsesFinal _ _ (E.light t i)
  by_cases c:E.clear i
  · have h:E.light t i=E.nominal t i:=funext fun U=>by simp [Lamps.light,c]
    rw [h]
    exact ⟨l.symmetry,l.borel,fun U V agree _=>l.sites U V agree⟩
  have h:E.light t i=masked p.threshold (E.ground i) (E.nominal t i):=funext fun U=>by simp [Lamps.light,c]
  rw [h]
  refine ⟨?_,masked_measurable _ _ _ l.borel,?_⟩
  · intro g U
    have gaugeLaw:Healthy p.threshold (E.ground i) (gauge g U) ↔ Healthy p.threshold (E.ground i) U:=by
      simp [Healthy]
    by_cases clear:Healthy p.threshold (E.ground i) U
    · rw [masked_eq _ _ _ _ (gaugeLaw.mpr clear),masked_eq _ _ _ _ clear,l.symmetry g U]
    rw [masked_ne _ _ _ _ (mt gaugeLaw.mp clear),masked_ne _ _ _ _ clear]
  intro U V agree flags
  have same:Healthy p.threshold (E.ground i) U ↔ Healthy p.threshold (E.ground i) V:=by
    change E.ground i ∩ RG.flags p.threshold U=E.ground i ∩ RG.flags p.threshold V at flags
    simp only [Healthy,Finset.disjoint_iff_inter_eq_empty,flags]
  by_cases yes:Healthy p.threshold (E.ground i) U
  · rw [masked_eq _ _ _ _ yes,masked_eq _ _ _ _ (same.mp yes),l.sites U V agree]
  rw [masked_ne _ _ _ _ yes,masked_ne _ _ _ _ (mt same.mpr yes)]

def shortRegular (w:V→ℝ)(a:V)(D:ℕ)(t:T)(U:Config G n):ℂ:=
  ∑'i:ι,if coverNumber p.B (L.ground i)≤D then (w a:ℂ)*(L.frame i t U).part (C.fire a) else 0

theorem short_regular_tail {w:V→ℝ}(wp:∀v,0<w v){σ c:ℝ}(paid:L.Paid w p.B σ c)
    (sn:0≤σ)(a:V)(D:ℕ)(t:T)(U:Config G n):
    ‖(w a:ℂ)*(L.log t U).part (C.fire a)-shortRegular L w a D t U‖≤Real.exp (-(σ*D))*c:=by
  let row:=fun i=>(w a:ℂ)*(L.frame i t U).part (C.fire a)
  let near:Set ι:={i|coverNumber p.B (L.ground i)≤D}
  have all:Summable row:=
    (((paid.sums sn wp t U).hasSum.mapL (Poly.get (C.fire a))).summable).mul_left (w a:ℂ)
  have ex:(w a:ℂ)*(L.log t U).part (C.fire a)=(∑'i,row i):=by
    rw [Lamps.log,Poly.share (paid.sums sn wp t U),tsum_mul_left]
  have half:shortRegular L w a D t U=∑'i,near.indicator row i:=by
    apply tsum_congr;intro i
    by_cases c:coverNumber p.B (L.ground i)≤D
    · rw [if_pos c,Set.indicator_of_mem (show i∈near from c)]
    rw [if_neg c,Set.indicator_of_notMem (show i∉near from c)]
  have cut:(∑'i,row i)=(∑'i,near.indicator row i)+(∑'i,nearᶜ.indicator row i):=by
    rw [←(all.indicator near).tsum_add (all.indicator nearᶜ)]
    apply tsum_congr;intro i;by_cases m:i∈near <;> simp [m]
  rw [ex,half,cut,add_sub_cancel_left]
  have wallet:=lamp_budget L paid wp (C.fire a) (mark:=a) (by simp [Census.fire]) (fun _=>t) (fun _=>U)
  let A:=Real.exp (-(σ*D))
  have bill:SumBudget (fun i=>‖nearᶜ.indicator row i‖) (A*c):=by
    apply budget_mono (budget_scale (Real.exp_nonneg _) wallet) (fun _=>norm_nonneg _)
    intro i
    by_cases m:i∈near
    · rw [Set.indicator_of_notMem (show i∉nearᶜ from fun h=>h m),norm_zero]
      exact mul_nonneg (Real.exp_nonneg _) (wallet.1 i)
    rw [Set.indicator_of_mem (show i∈nearᶜ from m)]
    have wide:D≤coverNumber p.B (L.ground i):=Nat.le_of_lt (Nat.lt_of_not_ge m)
    have d:0≤ -(σ*(D:ℝ))+σ*coverNumber p.B (L.ground i):=by
      have t:=mul_le_mul_of_nonneg_left (Nat.cast_le.mpr wide : (D:ℝ)≤_) sn;linarith
    have factor:1≤A*Real.exp (σ*coverNumber p.B (L.ground i)):=by
      dsimp only [A];rw [←Real.exp_add];exact Real.one_le_exp d
    change ‖(w a:ℂ)*(L.frame i t U).part (C.fire a)‖≤A*(_*Real.exp _)
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (wp a).le,Poly.solo_toll]
    exact (le_mul_of_one_le_right (mul_nonneg (wp a).le (norm_nonneg _)) factor).trans_eq (by ring)
  exact (norm_tsum_le_tsum_norm bill.2.1).trans bill.2.2

end YM.Integration.FVA1Physical.Exchange.RoseCut
