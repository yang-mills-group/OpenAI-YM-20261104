import YM.Comparison.RG02.Bare.Decay
/-! # Combining Laplace core with genuine complement test
 Handles ANY compatible `W` for this top step -- not defining top-physical field basis here.
 Real and formal prefactors **not** omitted in raw equality.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Bare
open Function Filter Finset MeasureTheory ProbabilityTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Marker Multi Order YM.Next.SectorChange Integral Actual Laplace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
  (K : Bulk.Kernel S p P O) (F : Forest S.ratio)
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} (W : Bulk.Colors R G f)
    (t : S.Choices) (x : fieldDir G c 1) (n : ℕ) (D : BudgetPoint)
local notation "I"=>Precision.Key F G → ℝ
local notation "g₀" g:max=> temperature g
local notation "S'" g:max=>Complex.ofReal (office K F t g 0 x)
local notation "W'" t:max g:max=>Complex.ofReal (wage K F t g 0 x)
local notation "Y"=> F.Slice G

def Witnessed (W : Bulk.Colors R G f) (K : Bulk.Kernel S p P O) := Bulk.Well W ∧ Starts W ∧ ∀ t, top W t=model t 0 W K -- `_` causes K unused/extra? syntax
-- relative to each tag share scalar, no θ independence required for other operations.
def forTag (t : S.Choices) (g : ℝ) := (Complex.ofReal (wage K F t g 0 x))⁻¹ • charge (prior G f) (Actual.stack t (sample g x) (g₀ g) (top W g))
variable (hW : Witnessed (V:=V) W K)
include hW D
-- strict support via interior; cutoff holds against g of thermal germ. Doesn't assert
-- asymptotic action with g_j calibrating schedule.
lemma fortune (s : R.Mode) : Trial (detail (Bulk.Fk K F t W x n) s) (fun g=> (forTag K F W x t g).part s) n := by
   obtain ⟨A,hA,ho,B⟩:= one_look K F 0 W x D n hW.1 t s
   have hn := (B A (Set.Subset.refl _) ho.measurableSet hA).2
   have hx:= perpetual hW.2.1 F t A x K s ho hA (n+1)
   have he (v : ℝ) := (leaf_model K v 0 W hW.1)
   have hh(g): forTag K F W x t g= portal K F t 0 W x (fun _=> A) g + (W' t g)⁻¹ • charge (F.order G) (Integral.outside F t g x A (top W g)):= by
       let M:= model g 0 W K
       let U:= Actual.stack t (sample g x) (g₀ g) M
       unfold forTag portal Integral.outside
       rw [hW.2.2,pack F t _ _ K.branches (he g) (model_gauge K g 0 W hW.1)]
       change (W' t g)⁻¹ • charge _ (U∘_)=_
       rw [split_cost (good_slice F t (sample g x) (g₀ g) K.branches (he g)) ho.measurableSet,smul_add]
   unfold Trial at *
   refine bill_congr ?_ (bill_add hn hx)
   filter_upwards with g; rw [Pi.sub_apply,hh]; simp only [Pi.add_apply,Pi.sub_apply,Poly.part_plus]; abel

def realMoment (g : ℝ) := (S' g)⁻¹ • Actual.Push S (g₀ g) (top W g) (sample g x)
omit D in
lemma moments (g : ℝ) : realMoment K F W t x g= (↑(count S):ℂ)⁻¹ • ∑ t:S.Choices,forTag K F W x t g:= by
  unfold realMoment forTag
  rw [agreed _ _ K.branches ( by rw [hW.2.2]; exact leaf_model K g 0 W hW.1)]
  have h (u : S.Choices) := office_choice K F t g 0 x u
  simp only [Finset.smul_sum]; apply Finset.sum_congr rfl; intro u _
  rw [← mul_smul ( ↑(count S):ℂ)⁻¹]; unfold wage; rw [Complex.ofReal_div, ← h u,Complex.ofReal_natCast,inv_div]; congr 1
  field_simp [show (↑(count S) : ℂ)≠0 by exact_mod_cast count_pos.ne'] -- natCast y defeq real? field_simp maybe

lemma header (s : R.Mode): Trial (detail (Bulk.Fk K F t W x n) s) (fun g=> (realMoment K F W t x g).part s) n := by
   let q:= peval (detail (Bulk.Fk K F t W x n) s) n
   let h (u : S.Choices) (g : ℝ):= (forTag K F W x u g).part s-q g
   have he(u): Bill (n+1) (h u):= by unfold h q; rw [Bulk.fkChoice K F t W x n u]; exact fortune K F W u x n D hW s
   have ht:= bill_smul ((↑(count S):ℂ)⁻¹) (bill_sum Finset.univ h fun i _=> he i)
   refine bill_congr ?_ ht; filter_upwards [eventually_pos] with g hg
   change _= (realMoment K F W t x g).part s-q g; rw [moments K F W t x hW _]
   simp only [Pi.smul_apply,Finset.sum_apply,h,Poly.part_smul,Poly.part_sum,smul_eq_mul,sum_sub_distrib]
   rw [Finset.sum_const, Finset.card_univ,nsmul_eq_mul, mul_sub,show Fintype.card S.Choices=count S from rfl, inv_mul_cancel_left₀]; exact_mod_cast count_pos.ne' -- defeq cast
-- cost consumers apply Trial.Fleet.Exp etc separately (real price vs signed vacuum).
end YM.Comparison.RG02.Bare
