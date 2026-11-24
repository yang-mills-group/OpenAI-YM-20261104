import YM.GradedFar.Street
/-!
# Towards G.9(i): Derivatives of the PREDICTED formal values from earlier physical hypothesis

Use in Earn derivative extension. FTC before comparing derivative of the **physical** Y:
we already know each line identity from uniform *compact value* receipts & charging
budgets for differentiation against our Gram probes. Use them here, no assumption of formal smoothness bridge.
Point queries, not motion at (r,T) through the derivative.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff
open Function Filter Set PowerSeries MeasureTheory
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Fleet MS.Menus
open scoped Topology BigOperators Classical ContDiff
namespace Sunshine
variable {n h m : ℕ}
local instance {n:ℕ} : ContinuousSMul ℝ (Points n):= IsBoundedSMul.continuousSMul
open Metric Asymptotics
local notation "Bt"=> Points n
private lemma increment_cmp {f:Bt→ℂ}{g:Bt→ (Bt→L[ℝ]ℂ)} (X:Set Bt)(hX:IsOpen X) (hg:ContinuousOn g X)
    (H:∀ x v:Bt, MapsTo (slopePath x (v-x)) (uIcc (0:ℝ) 1) X → f v-f x= ∫ u in (0:ℝ)..1,g (slopePath x (v-x) u) (v-x))
    {x:Bt}(hx:x∈X) : HasFDerivAt f (g x) x :=by
 apply HasFDerivAt.of_isLittleO; refine isLittleO_iff.mpr (fun ε he=>?_)
 have hSnow:= (hg.continuousAt (hX.mem_nhds hx)).tendsto.eventually (ball_mem_nhds (g x) he); obtain ⟨d,hd,h⟩:= Metric.mem_nhds_iff.mp (inter_mem (hX.mem_nhds hx) hSnow)
 filter_upwards [ball_mem_nhds x hd] with v (hv: v∈Metric.ball x d)
 let θ:=slopePath x (v-x); have Hq (u:ℝ)(hu:u∈uIcc (0:ℝ) 1): θ u∈Metric.ball x d:= by
    rw [uIcc_of_le zero_le_one] at hu; rw [mem_ball, dist_eq_norm]; unfold θ; rw [slopePath, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hu.2) (by simpa [dist_eq_norm] using Metric.mem_ball.mp hv)
 have hθ:MapsTo θ (uIcc (0:ℝ) 1) X:= fun u hu=> (h (Hq _ hu)).1
 let A:= fun u:ℝ=> (g (slopePath x (v-x) u)) (v-x); have hv':IntervalIntegrable A volume 0 1:= ((hg.comp (walking_cont x (v-x)).continuousOn hθ).clm_apply continuousOn_const).intervalIntegrable
 rw [H x v hθ]; change ‖(∫ u in (0:ℝ)..1, A u) - _‖ ≤ _
 apply le_trans ?_ (Crosser.int_budget (fun u=> A u-g x (v-x)) ?_); swap
 · intro u hu; obtain hi:=h (Hq _ hu); have hh:‖g (θ u)-g x‖ ≤ ε := le_of_lt (show ‖_‖ < ε from (by simpa [dist_eq_norm] using Metric.mem_ball.mp hi.2))
   exact ((g (θ u)-g x).le_opNorm (v-x)).trans (mul_le_mul_of_nonneg_right hh (norm_nonneg _))
 rw [show (∫ u in (0:ℝ)..1,A u)-g x (v-x)=(∫ u in (0:ℝ)..1, A u-g x (v-x)) by rw [intervalIntegral.integral_sub hv' intervalIntegrable_const]; simp]
variable {G:Gauge} (α:Future G h)(V:Arenas G)
-- one dimension along predicted direction partial gradient
-- keep coefficient evaluated at same position even before ground. cap grown.
def iris_one (l:Fin n×Axis)(u:ListInput G n h)(x:Points n) : PowerSeries ℂ := ∑ j: Toon G (h+1),
    α l.2 (u l.1) j * sent V (h+1) x (update (climbing u) l.1 (theory j))
def ticketOne (l: Fin n×Axis) : Bt→L[ℝ]ℂ := LinearMap.toContinuousLinearMap {
    toFun:= parallel l
    map_add' x y:= by simp [parallel]
    map_smul' _ _:= by simp [parallel, Complex.real_smul]
}
private lemma turn_zero (a b:Fin n×Axis)(h:a≠b): ticketOne a (Points.direction b.1 b.2)=0:= by
 change parallel _ _ = _; unfold parallel Points.direction
 by_cases hp:a.1=b.1
 · have ht:a.2≠b.2:= fun hh=> h (Prod.ext hp hh); simp [hp,ht,basis]
 simp [hp]
def specTariff (u:ListInput G n h)(k:ℕ)(x:Bt) : Bt→L[ℝ]ℂ := ∑ a: Fin n×Axis, (coeff k (iris_one α V a u x)) • ticketOne a
lemma projected (u:ListInput G n h)(k:ℕ)(v x:Bt) : specTariff α V u k x v=coeff k (SpecCost α V v x u):= by
 simp_rw [specTariff, SpecCost, map_sum,_root_.sum_apply, coeff_C_mul, _root_.smul_apply, smul_eq_mul]; refine Finset.sum_congr rfl fun _ _=>?_ ; rw [mul_comm]; rfl
lemma change_order (i:Fin n×Axis)(u: ListInput G n h)(x:Bt)(k:ℕ) : specTariff α V u k x (Points.direction i.1 i.2)=coeff k (iris_one α V i u x):= by
 rw [specTariff, _root_.sum_apply,Finset.sum_eq_single i]; simp only [_root_.smul_apply,smul_eq_mul]
 change _ * parallel _ _ = _; simp [parallel,Points.direction,basis]
 · intro j _ hh; rw [_root_.smul_apply, turn_zero j i hh,smul_zero]
 simp
variable {C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J:ℝ→tower S)
variable (Z: WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H: Main.Match Z hG M σ true)
local notation "X" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
include H
lemma spec_cont (u:ListInput G n h)(k:ℕ): ContinuousOn (specTariff α X u k) (conf n) := by
    unfold specTariff; refine continuousOn_finsetSum Finset.univ fun i _=>?_
    have hf:ContinuousOn (fun x=> coeff k (iris_one α X i u x)) (conf n):= by simp_rw [iris_one,map_sum, coeff_mul,sent,coeff_mk]; exact continuousOn_finsetSum _ (fun _ _=> continuousOn_finsetSum _ (fun _ _=> (kernel_continuous Z M H _ _).const_mul _))
    exact hf.smul (continuousOn_const (c:=ticketOne i))
variable {t:ℝ→ℝ}(ht:Coupling G t)(hμ: Neighbor.Included F J h (h+1) (Nat.le_succ h))(hX:ClassExpansion F J (Scale.Measure.outlook Z.scheme Z.criterion) t n h)
    (hX':ClassExpansion F J (Scale.Measure.outlook Z.scheme Z.criterion) t n (h+1))(hα:PaidFuture F J α t)
include ht hμ hα hX hX'
lemma glow_at {x:Points n}(hx:x∈conf n)(u:ListInput G n h)(k:ℕ): HasFDerivAt (fun x=> coeff k (sent X h x u)) (specTariff α X u k x) x:=by
 refine increment_cmp (conf n) (conf_open _) (spec_cont α Z M H u k) (fun x v he=>?_) hx
 simp_rw [projected]; obtain H:= congrArg (coeff k) (fixedLine F J Z M H α ht hμ hX hX' hα x (v-x) he u); rw [operand,coeff_mk,Crosser.endsZero,Crosser.endsOne,map_sub] at H; exact H
lemma exposed {x:Points n}(hx:x∈conf n)(u:ListInput G n h)(k:ℕ)(i:Fin n×Axis) : Points.gradient i.1 i.2 (fun x=> coeff k (sent X h x u)) x=
    coeff k (iris_one α X i u x):= by
 exact (congrArg (fun f:Points n→L[ℝ]ℂ=> f (Points.direction i.1 i.2)) (glow_at α F J Z M H ht hμ hX hX' hα hx u k|>.fderiv)).trans (change_order ..)
end Sunshine
end YM.Integration.GradedFar.Tariff
