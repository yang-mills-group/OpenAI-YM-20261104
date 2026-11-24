import YangMills.WilsonProof.NativeSupport.Commissioned259.Matched
/-! # (F.2), used in pricing (M.1). On this independently constructed `start`.
- No extra hypothesis about a family solving position equations or from a free
  calculation. Use the **formal** purchase from Match. Point operands & finite
  polynomial smear in our actual cropping convention. Real-linear Screen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Pose
open Function Filter Set PowerSeries MeasureTheory
open Maxwell XSpace XSpace.Normalize XSpace.Structure1
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open scoped Topology ContDiff BigOperators Classical
open FVA2.Scale O.Score Dframe

variable {G : Gauge} {n d q : ℕ} (N : WilsonPrescription G) {sim : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
local notation "W" => Scale.Measure.start N.scheme N.criterion
local notation "RoseK" => N.criterion
local notation "T" => Reg.Faith.reports 0 RoseK M
local notation "V" => N.store
include H

lemma orders : Jury.Orders (W d) (T d) := by
  let P := H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  exact Jury.enrolled 0 M _ _ _ sim P.Taylor P.still P.base

lemma begins : Equator.StarGround (W d) := by
  let P := H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  exact Scale.Measure.dawn N.scheme RoseK 0 M _ sim P.Taylor P.still P.base

lemma F2 (k : ℕ) : (N.store.measure d).D (T d k) = if k=0 then (N.store.measure d).D (reference G d) else 0 := by
  let P := H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  let X := PowerSeries.X (R:=ℂ)
  have hx := Jury.solved 0 M N.scheme RoseK σ sim P.Taylor P.still P.base
    (p:=X) (d:=d) (by simp [Program.Rooted,X]) (by unfold Reg.Unique.CoreR; simp [X]) k
  rw [deck0, Normalize.author] at hx
  have hs := (orders N M H (d:=d)).glance X
  rw [Facets.team_one] at hs
  rwa [Jury.peer (W d) (Program.substitute X (T d)) hs.exact (orders N M H).exact] at hx

lemma blanking : T d 0 = reference G d := by
  ext1 n; ext1 a; ext u
  rw [(orders N M H).exact n 0,XSpace.Normalize.reflects]
  refine Test.apply_eq _ fun x hx=>?_ ; rw [Jury.fxt,dif_pos hx, begins N M H]

/-- Connected formula on physical and regulator sides. Definitionally the triple
value of §A `WilsonPositionThermometerConnected`. -/
def log3 (A : Rose.Badge → ℂ) : ℂ :=
  A Finset.univ - (A {0,1}*A {2} + A {0,2}*A {1} + A {1,2}*A {0}) +
    2*(A {0}*A {1}*A {2})
lemma meter_null {x : Points 3} (hx : x∈conf 3) : coeff 0 (Scale.Select.Single (W 6) x)=0 := by
  have all (s:Rose.Badge) (hh:s.Nonempty) : constantCoeff (Rose.batchT (Jury.fxt (W 6) x) s) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply,Rose.batchT,coeff_mk,Jury.fxt,dif_pos hx,begins N M H]
    exact Rose.silent N.scheme sim hx s hh
  rw [coeff_zero_eq_constantCoeff_apply]
  simp only [Select.Single,Rose.b3,two_smul,map_add,map_mul,map_sub]
  have a := all Finset.univ (by decide)
  simp only [a, all {0} (by decide), all {1} (by decide), all {2} (by decide),mul_zero,zero_add,sub_zero]

lemma F2_meter : Scale.Select.output RoseK (W 6)=(Rose.c_T RoseK:ℂ) • PowerSeries.X := by
  have z : coeff 0 (Scale.Select.output RoseK (W 6))=0 := by
    rw [Select.output,coeff_mk]
    have h := (Rose.test RoseK).apply_eq (P:=fun _=>0) (K:=fun x=>coeff 0 (Scale.Select.Single (W 6) x)) (fun x hx=> meter_null N M H hx)
    rw [h]; simp [Test.applyTo]
  have he := H.details.toServed.toPosted.toQuoted.toContract.meant
  rw [Select.meter,Reg.Choice.tune,z,map_zero,sub_zero] at he
  rw [←he]
  rw [smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr N.criterion.fresh.ne),one_smul]

omit H
variable {A : Way G d} (x : Points n) (u : Tags G d n) (L : XSpace.Normalize.Reports G d)
/-- Point array at t using only the hypothesis-free formal coefficients. -/
def array (A : Way G d) (x : Points n) (q : ℕ) (t : ℝ) : Structure1.Point G d n :=
  ∑ k ∈ Finset.range (q+1), (t:ℂ)^k • Jury.fxt A x k

lemma array_eq (q : ℕ) (t : ℝ) : array A x q t u = crop q t (PowerSeries.mk (fun k=>Jury.fxt A x k u)) := by
  simp_rw [crop_apply, array,_root_.sum_apply,_root_.smul_apply,coeff_mk,smul_eq_mul]

lemma array_smooth (th : Jury.Thin A) (u : Tags G d n) (q : ℕ) (t : ℝ) : ContinuousOn (fun x=> array A x q t u) (conf n) := by
  simp_rw [array_eq,crop_apply,coeff_mk]
  exact continuousOn_finsetSum _ fun i _=> (th n i u).const_mul _

def bundle (L : XSpace.Normalize.Reports G d) (q : ℕ) (t : ℝ) : XSpace.Normalize.Prediction G d := ∑ k∈ Finset.range (q+1), t^k • L k
lemma bundle_val (q : ℕ) (t : ℝ) (a : Test n) : bundle L q t n a u=∑ k∈Finset.range (q+1), (t:ℂ)^k * L k n a u := by
  simp only [bundle, Finset.sum_apply, Pi.smul_apply, LinearMap.sum_apply, LinearMap.smul_apply, _root_.sum_apply, _root_.smul_apply, Complex.real_smul, Complex.ofReal_pow]
lemma tests_point (hL : Jury.Orders A L) (q : ℕ) (t : ℝ) (a : Test n) :
    bundle L q t n a u=a.applyTo (fun x=>array A x q t u) := by
  simp_rw [bundle_val,array_eq,crop_apply,coeff_mk,hL.exact n, Test.applyTo,Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _=>?_
    rw [← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall fun x=> by ring)
  intro i _; exact a.smearing ((hL.light n i u).const_mul _)

include H
lemma positioned (q : ℕ) (t : ℝ) : (N.store.measure d).D (bundle (T d) q t) = (N.store.measure d).D (reference G d) := by
  rw [bundle,map_sum]; simp_rw [map_smul,F2 N M H]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i hi h; rw [if_neg h,smul_zero]
  simp
end YM.FVA2.GradedFar259.Pose
