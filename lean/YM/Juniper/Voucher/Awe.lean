import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Carries
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Haul

set_option autoImplicit false
noncomputable section
namespace YM.Juniper.Voucher
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Marlin
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Poll Pond MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Metric Progress.DirectedRecipe Payments Ovens Ovens.Pipes
open Refrain Trio
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L:Side} (B : BudgetPoint) (C : Listing G c) (z w : ℕ) {p d a δ q Y E : ℝ}
variable (T : Collection.Source G c) (g t:Trio.Offer G c) (V:Config G c)
local notation "A"=> lodge C z w
-- retain the FULL oriented soft inventory in the tax. unit per Door, SIGN already Bison's. clients don't re-smear with a new averaged support.
def tax := ∑ i: Door c, choir (-t) i V
lemma taxes (u:Offer G c): tax (u+t) V= tax u V + tax t V ∧ tax (u-t) V=tax u V-tax t V:= by
    constructor
    · unfold tax; rw [←sum_add_distrib]; refine sum_congr rfl fun i _=>?_ ; change Rim c * (-(u _ _+t _ _)) =_*(-_)+_* (-_); ring
    unfold tax; rw [←sum_sub_distrib]; refine sum_congr rfl fun i _=>?_ ; change Rim c * (-(u _ _- t _ _)) =_*(-_)-_* (-_); ring
lemma exactTax : ∑' i,(bison T g t).logarithm i V=tax t V:= by
    let f' : Civ c→ℝ:= Sum.elim 0 (fun i=> choir (-t) i V); let y:=leanU c
    have he : ∑' i,(bison T g t).logarithm i V=∑' i, f' (y i):= by refine tsum_congr (fun i=>?_); change Sum.elim (fun _:ℕ=> (0:Config G c→ℝ)) (choir (-t)) (y i) V=_; cases y i <;> rfl
    rw [he,y.tsum_eq f', Summable.tsum_sum (f:=f') (show Summable (fun i : ℕ=> f' (.inl i)) from summable_zero) Summable.of_finite]; simp [f',tax]
local notation "F̂"=> (bison T (0:Offer G c) t)
local notation "B'"=> pluck B A
lemma zeroBill (he: Meadow.Budget B C.reg T.logRead a):
    (((B').read (poursP B (A) (F̂))).additive B V)= ((C.read T).additive B V):=by
    let y := leanU c; let f'(i:Civ c) := Sum.elim (fun i=>(C.read T).regularOccurrence B i V) 0 i
    have hh : ∀ i:Civ c, ((B').read (poursP B (A) F̂)).regularOccurrence B (y.symm i) V=f' i := by
       intro i; change masked _ (Sum.elim C.reg (sea z) (y (y.symm i))|>.support) (Sum.elim _ _ (y _)) _= _; rw [Equiv.apply_symm_apply]; cases i; rfl
       next i=> change masked _ _ (Song.choir (0:Offer G c) i) V=0; simp [Song.choir,masked]
    have hv : ((B').read (poursP B A F̂)).additive B V=∑' i,f' i:=by rw [← y.tsum_eq f']; unfold Activities.additive; refine tsum_congr fun i=>?_ ; rw [← hh,Equiv.symm_apply_apply]
    rw [hv,Summable.tsum_sum (f:=f') (Marlin.stashes B C T _ he) Summable.of_finite]; dsimp only [f', Sum.elim_inr,Sum.elim_inl]; simp only [Pi.zero_apply]; rw [tsum_zero, add_zero]; rfl

variable (β τ φ x:ℝ) (P₀:PathData G)(W:Clip) (R:Listing G c)(f:Collection.Source G c)
local notation "u!"=> Collection.earlyValue
lemma finality (hv:R.hard=C.hard)(ht:f.hardRead=T.hardRead)(hh:Meadow.Budget B C.reg T.logRead a)
    (hF:Ingredients (lodge C z w) (dummy (bison T 0 t)) (raiser B) 0 q)
    (he : (R.read f).additive B V=(C.read T).additive B V+x*Fintype.card (Site c) - tax t V) :
    u! R P₀ W B f β τ φ V=u! (B') P₀ W B (poursP B A F̂) β (τ-x) φ V:=by
    have hS : (Collection.frozen R P₀ W B f β τ).exponent V=(Collection.frozen (B') P₀ W B (poursP B A F̂) β (τ-x)).exponent V+tax t V:= by unfold Rep.exponent; dsimp only [Collection.frozen]; rw [he,zeroBill _ C z w T t V hh]; ring
    have hG: ((B').read (poursP B A F̂)).gas B V=(R.read f).gas B V * Real.exp (tax t V) := by
       rw [pulpy_T hF, exactTax]; congr 1; let X:=(A).pours F̂; let K:=R.read f
       unfold Activities.gas; refine tsum_congr fun i=>?_ ; have ha:X.admissible B V i↔ K.admissible B V i:= by unfold Activities.admissible; rw [show K.forced = X.forced from hv]
       unfold Activities.gasOccurrence; rw [propext ha]; split; next _=> exact prod_congr rfl fun i _=> congr_fun (congr_fun ht i).symm V
       rfl
    unfold Collection.earlyValue Rep.eval; rw [hS,Real.exp_add]; dsimp only [Collection.frozen] at *; rw [hG]; ring

-- locality ledger for *halo move stamps* only, no derivative assumptions here
structure LightTax (B : BudgetPoint) (w:ℕ) (t : Offer G c) (T : ℝ) : Prop where
   tidy (i:Site c) : Tidy B (neighbors w i) (t i)
   failed (i : Site c) (V : Config G c) : Healthy B.threshold (neighbors w i) V → t i V=0
   bills (i : Site c) (V : Config G c): ‖t i V‖ ≤ T
variable {B g z w t}
lemma LightTax.reaches (h:LightTax B z g E)(hz:z≤w) : LightTax B w g E:= by
   have hh(i:Site c) : neighbors z i⊆ neighbors w i:=fun t ht=> (neighbors_mem ..).2 (((neighbors_mem ..).1 ht).trans hz)
   refine ⟨fun i=> ?_,fun i V hv=> h.failed _ _ (hv.mono_left (hh i)), h.bills⟩
   have hq:= h.tidy i; refine { hq with uses:= fun x y hx he=> hq.uses x y (agrees_mono hx (hh i)) ?_ }; rw [← Finset.inter_eq_left.mpr (hh i),Finset.inter_assoc,he,← Finset.inter_assoc] -- maybe type
lemma LightTax.more (h:LightTax B w g E) (hv:LightTax B w t q): LightTax B w (g+t) (E+q) ∧ LightTax B w (g-t) (E+q):= by
    constructor
    · refine ⟨fun i=> ?_, fun i V he=> by simp [h.failed i _ he, hv.failed i V he], fun i V=> (norm_add_le (g i V) (t i V)).trans (add_le_add (h.bills ..) (hv.bills ..))⟩; change Tidy B _ (g i+t i); rw [← sub_neg_eq_add,← zero_sub (t i)]; exact tidy_sub _ (h.tidy _) (tidy_sub _ (tidy_const ..) (hv.tidy _))
    exact ⟨fun i=> tidy_sub _ (h.tidy _) (hv.tidy _),fun i V he=> by simp [h.failed i V he, hv.failed i V he],fun i V=>(norm_sub_le (g i V) (t i V)).trans (add_le_add (h.bills ..) (hv.bills ..))⟩
end YM.Juniper.Voucher
