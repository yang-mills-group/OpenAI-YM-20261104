import YM.GradedFar.Intercept
/-!
# F.2 exact position identity & calibration cost in the adjusted contract

Reports for *pre-adjustment* `Before` series of Z, same datum even in hypotheses on physical W costs.
Keep Stock on Store & tests through all included caps & arities.
Consequences toward physical tested-log bound.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff.Ballot
open Function Filter Set PowerSeries MeasureTheory
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Fleet MS.Menus
open Billboard
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
variable {n h:ℕ}
local notation "KX"=> WilsonPrescription.criterion Z
local notation "A" => Scale.Measure.start (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "bill"=> Reg.Faith.reports 0 KX M h
local notation "Sat" => (Z.store.measure h)
local notation "c*" => Rose.cT (Z.criterion.cut) G Z.criterion.image
include H in
lemma receipt_position (k:ℕ) : (Sat).D (bill k)= if k=0 then (Sat).D (reference G h) else 0:= by
 have H₀:= Tangent.unit; have hb:= H.details.toServed.toPosted.toQuoted.toContract.toMission.born
 have ht:= (Jury.solved (d:=h) 0 M Z.scheme Z.criterion σ hG hb.Taylor hb.still hb.base H₀.start H₀.real k)
 rw [deck0,Normalize.author,rules] at ht; convert ht using 2
 rw [Finset.sum_eq_single k] <;> (simp [cut,PowerSeries.coeff_X_pow] <;> aesop)

-- important for lim Snap at t'→0
include H in
lemma receipt_ground : bill 0=reference G h := by
 ext n φ v; rw [(till_reports Z M H).exact n 0 φ v,reflects];
 apply Test.apply_eq; intro x hx; dsimp only; rw [Jury.fxt,dif_pos hx,before0 Z M H]

def goal (h:ℕ)(q:ℕ)(r:ℝ) := ∑ k∈Finset.range (q+1), r^k • Reg.Faith.reports 0 KX M h k
include H
lemma goal_ground (q:ℕ) : goal Z M h q 0=reference G h:= by rw [goal,Finset.sum_eq_single 0,pow_zero,one_smul,receipt_ground Z M H]; exacts [fun i _ he=> by rw [zero_pow he, show (0:ℝ) • Reg.Faith.reports 0 KX M h i=0 from (by ext n t x; change (0:ℝ) • ((Reg.Faith.reports 0 KX M h i) n t x)= (0:ℂ); exact zero_smul ℝ _)],by simp]
lemma goal_metric (p:ℕ)(u:ℝ) : (Sat).D (goal Z M h p u)= (Sat).D (reference G h):= by
 simp_rw [goal,map_sum,map_smul,receipt_position Z M H]; rw [Finset.sum_eq_single 0]; exacts [by simp,fun i _ hi=> by simp [hi],by simp]
set_option linter.unusedSectionVars false in
lemma extinct (v: ListInput G n h){x:Points n}(hx:x∈conf n)(i:ℕ):
    Jury.fxt (A h) x i v= coeff i (sent A h x v) := by
 rw [cashed _ _ hx, Jury.fxt, dif_pos hx]
-- smeared positions S.answer vs goal
lemma usable (φ:Test n) (v:ListInput G n h)(q:ℕ)(r:ℝ):
    goal Z M h q r n φ v = φ.applyTo (fun x=>appointedH140Crop q r (sent A h x v)):= by
 let V : Window G h := ⟨n,φ,v⟩
 have hm i:= (till_reports Z M H).exact n i φ v; change watch V (goal Z M h q r)=_
 simp_rw [goal,map_sum,map_smul, show ∀ i,watch V (bill i)=_ from hm]
 rw [Test.apply_eq φ (show EqOn (fun x=>appointedH140Crop q r (sent A h x v)) (fun x=>∑ i∈Finset.range (q+1),(r:ℂ)^i*Jury.fxt (A h) x i v) (conf n) from fun x hx=> by
    dsimp only; simp_rw [crop_eq,extinct Z M H v hx])]; unfold Test.applyTo; simp_rw [Finset.mul_sum]; rw [integral_finsetSum]
 · refine Finset.sum_congr rfl fun j _=>?_ ; rw [Complex.real_smul, Complex.ofReal_pow,← integral_const_mul]; apply integral_congr_ae; filter_upwards with a; ring
 intro j _; exact φ.smearing (((till_reports Z M H).light n j v).const_mul _)
lemma calm (v:ListInput G n h)(i:ℕ): ContinuousOn (fun x=>coeff i (sent A h x v)) (conf n):=
 ((till_reports Z M H).light n i v).congr (fun _ hx=> (extinct Z M H v hx i).symm)
lemma sheltered (v:ListInput G n h)(p:ℕ)(r:ℝ): ContinuousOn (fun x=>appointedH140Crop p r (sent A h x v)) (conf n):= by
 simp_rw [crop_eq]; exact continuousOn_finsetSum _ (fun i _=> (calm Z M H v i).const_mul _)

abbrev MASK := Rose.missing (Rose.tag G)
local notation "peak"=> Select.Single (A 6)
lemma extinct_mask (s:Rose.Badge){x:Points 3}(hx:x∈conf 3): Rose.batchT (Jury.fxt (A 6) x) s=sent A 6 x (MASK (G:=G) s):= by ext k; rw [Rose.batchT,coeff_mk]; exact extinct Z M H _ hx k
set_option linter.unusedSectionVars false in
lemma unlocked (φ:Test n){f:Points n→ℂ} (hf:∀ x∈conf n,f x=0): φ.applyTo f=0:=by rw [Test.apply_eq φ (show EqOn f 0 _ from hf)]; simp [Test.applyTo]
lemma vacant_zero {x:Points 3}(hx:x∈conf 3): coeff 0 (peak x)=0:= by
 let m:= Rose.batchT (Jury.fxt (A 6) x); have hF(i:Rose.Badge)(hp:i.Nonempty): constantCoeff (m i)=0:= by
    rw [← coeff_zero_eq_constantCoeff_apply]; unfold m; rw [extinct_mask Z M H i hx,cashed A _ hx,before0 Z M H]; exact Rose.silent Z.scheme hG hx i hp
 rw [coeff_zero_eq_constantCoeff_apply]; change constantCoeff (Rose.b3 m) = _; rw [Rose.b3]; simp only [two_smul,map_add,map_sub,map_mul]; rw [hF {1,2},hF {0,2},hF {0,1},hF {0},hF {1},hF {2},hF Finset.univ]; simp
 all_goals decide
lemma exact_signal (k:ℕ): (Rose.test KX).applyTo (fun x=> coeff k (peak x))= coeff k (((c*:ℝ):ℂ) • X):= by
 by_cases hk:k=0
 · subst k; rw [map_smul,coeff_X,if_neg (by simp),smul_zero]; exact unlocked Z M H _ (fun _ h=>vacant_zero Z M H h)
 have he:=congr_arg (coeff k) H.details.toServed.toPosted.toQuoted.toContract.meant
 rw [Select.meter,Reg.Choice.tune,map_smul,map_sub, coeff_C,if_neg hk,sub_zero,Select.output,coeff_mk] at he
 rw [map_smul, ← he, smul_inv_smul₀]; exact_mod_cast Z.criterion.fresh.ne
lemma signal_position (q:ℕ)(hq:1 ≤ q)(r:ℝ): (Rose.test KX).applyTo (fun x=> appointedH140Crop q r (peak x))= (c*:ℝ)* (r:ℝ) := by
 simp_rw [crop_eq,Test.applyTo,Finset.mul_sum]; rw [integral_finsetSum]
 · have he (i:ℕ): (∫ x:Points 3, Rose.test KX x*((r:ℂ)^i* coeff i (peak x)))= (r:ℂ)^i*coeff i (((c*:ℝ):ℂ) • X):= by
     rw [← exact_signal Z M H,Test.applyTo, ← integral_const_mul]; refine integral_congr_ae ?_; filter_upwards with x; ring
   simp_rw [he]; rw [Finset.sum_eq_single 1]; simp [mul_comm (r:ℂ)]; exacts [fun i _ hi=> by simp [PowerSeries.coeff_X,hi],by simp [show 0<q from hq]]
 intro i _; exact (Rose.test KX).smearing ((Select.steady _ (k:=i) (till_reports Z M H (h:=6)).light).const_mul _)
end YM.Integration.GradedFar.Tariff.Ballot
