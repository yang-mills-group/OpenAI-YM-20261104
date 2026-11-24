import YangMills.WilsonProof.NativeSupport.Commissioned259.Pose.Shop
/-! # PoseFit -- thermometer (F.3) at true physical W. **Relative to the isolated**
previous prices, including finite uses of the very strong physical input `(C5)`.
Use actual full connected map on physical & formal tag operands at exactly these locations,
recruit D tests, no independent-location estimate. This is for powering \(g\) in M2.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Pose
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury O.Score Comparing
open scoped Topology ContDiff Classical BigOperators

variable {G : Gauge} {d n q m e : ℕ} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (U : Final C f S) (J : ℝ→PhysMS.tower S) (hJ : Leading U J)
    (N : WilsonPrescription G) (A : ℝ→Change G d) (t : ℝ→ℝ)
variable {S0 : Finset Alcove} (V : C5 U J N A t S0 m q)
    (hz : requests N d ⊆ S0) (hp : normal U J N.store)
    {sim : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
local notation "late" => 𝓝[>] (0:ℝ)
local notation "FF" => Paper.point U J
local notation "W" => Scale.Measure.start N.scheme N.criterion
local notation "δ" => g0 G
local notation "a" => Rose.test N.criterion
local notation "fitting" => booth (tsupport (Rose.test N.criterion)) late
include H
lemma array_rises (h : e≤d) {x:Points n} (hx:x∈conf n) (u:Tags G e n) (q:ℕ) (s:ℝ) :
    array (W e) x q s u = array (W d) x q s (up h ∘ u) := by
  let P:= H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  have eq:= Scale.Measure.inherited N.scheme N.criterion 0 M σ sim P.Taylor P.still P.base h
  simp_rw [array_eq,crop_apply,coeff_mk,fxt,dif_pos hx, eq]

include V hz hp hJ
lemma six_price (he:6≤d) (u:Tags G 6 3) :
    (fun i:ℝ×Points 3=> FF i.1 6 3 i.2 u - array (W 6) i.2 q (t i.1) u)=O[fitting] fun i=>δ i.1^m := by
  have h:= bare_price U J N A t V hz hp M H (hz (pod N)) (up he ∘ u)
  refine h.congr' ?_ (EventuallyEq.refl ..)
  have x : Tendsto Prod.fst fitting late := tendsto_fst
  filter_upwards [x.eventually (Paper.pointing U J hJ (n:=3) he), placed] with i hi hv
  change _ = FF i.1 6 3 _ u - array (W 6) _ _ _ _
  have y : i.2∈conf 3:= (Rose.test N.criterion).tsupport_subset hv
  rw [hi u _ y,array_rises N M H he y]; rfl
omit V hz hp hJ
lemma receipt (r : ℝ) (hh : 1≤ q) : (Rose.test N.criterion).applyTo
    (fun x=> crop q r (Scale.Select.Single (W 6) x)) = (r:ℂ)*(Rose.c_T N.criterion : ℂ) := by
  have he : crop q r (Scale.Select.output N.criterion (W 6))=(r:ℂ)*(Rose.c_T N.criterion:ℂ) := by
    rw [F2_meter N M H,crop_apply,Finset.sum_eq_single 1]
    · simp
    · intro i _ H; rw [_root_.map_smul, PowerSeries.coeff_X, if_neg H,smul_zero,mul_zero]
    intro no; have f := no (Finset.mem_range.mpr (show 1<q+1 by omega)); exact False.elim f
  refine Eq.trans ?_ he; simp_rw [crop_apply,Scale.Select.output, coeff_mk,Test.applyTo,Finset.mul_sum]
  rw [integral_finsetSum]; · exact Finset.sum_congr rfl (fun i _=> by rw [← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall fun x=>by ring))
  intro i _; exact (Rose.test N.criterion).smearing ((Select.steady (W 6) (orders N M H).light).const_mul _)
-- General: have moment comparisons on the aperture of this criterion at all-six.
-- Can use on any comparison of our analytic purchases, e.g., the trial with another t'
-- arising in proof of (G.1). Need polynomial in true tags on BOTH sides.
-- X uses the formal start.W
variable {I:Type*} {F:Filter I} (s u : I→ℝ) {g : I→ℝ}
local notation "care" => booth (tsupport (Rose.test N.criterion)) F
abbrev ret (G:Gauge) (s:Rose.Badge) := Rose.missing (Rose.tag G) s
abbrev fox (x:Points 3) (t:ℝ)(q:ℕ)(s:Rose.Badge) := array (W 6) x q t (ret G s)
abbrev pie (x:Points 3) (t:ℝ)(q:ℕ) := crop q t (Scale.Select.Single (W 6) x)
variable (X : I→Points 3→Rose.Badge→ℂ)(D:I→Points 3→ℂ)
lemma aperture (hh : ∀ᶠ i in F, |s i| ≤ 1) (b:Rose.Badge) (q:ℕ) : (fun i:I×Points 3=>fox N i.2 (s i.1) q b) =O[care] home :=
  bounded_array (W 6) (orders N M H).light (a).hasCompactSupport (a).tsupport_subset placed (ret G b) q ( (tendsto_fst:Tendsto Prod.fst care F).eventually hh )
lemma ap_crop (ht:s=O[F] g) (hh : ∀ᶠ i in F, |s i| ≤ 1) (q:ℕ) :
    (fun i:I×Points 3=> log3 (fox N i.2 (s i.1) q)-pie N i.2 (s i.1) q)=O[care] fun i=>g i.1 ^ (q+1) := by
  let P (b:Rose.Badge)(i:I×Points 3):= Rose.batchT (fxt (W 6) i.2) b
  have F': Tendsto Prod.fst care F :=tendsto_fst; have h := logcrop q (ht.comp_tendsto F') (F'.eventually hh) P
    (fun b=> compact_tunes (W 6) (orders N M H).light (a).hasCompactSupport (a).tsupport_subset placed (ret G b))
  apply h.congr_left; intro i; unfold pie; congr 2
  ext1 b; exact Eq.symm (array_eq ..)

variable {w:I→ℝ}
  (cost:∀ b:Rose.Badge,(fun i:I×Points 3=>X i.1 i.2 b-fox N i.2 (s i.1) q b)=O[booth (tsupport (Rose.test N.criterion)) F] (w ∘ Prod.fst))
  (hw : w =O[F] home)
  (hq : (fun i=>g i^(q+1))=O[F] w) (ht:s=O[F] g) (hh:∀ᶠ i in F, |s i| ≤ 1)
  (hp0 : ∀ᶠ i in F,ContinuousOn (fun x=> log3 (X i x)) (conf 3))
include hw cost hh
lemma ap_bound (b : Rose.Badge) : (fun i:I×Points 3=>X i.1 i.2 b)=O[care] home := by
  have F': Tendsto Prod.fst care F :=tendsto_fst
  exact (((cost b).trans (hw.comp_tendsto F')).add (aperture N M H s hh b q)).congr_left (fun i=> sub_add_cancel ..)
include ht hq hp0
lemma relog :
    (fun i=> (a).applyTo (fun x=>log3 (X i x))- (a).applyTo (fun x=>pie N x (s i) q))=O[F] w := by
  have x (b:Rose.Badge) := ap_bound N M H s X cost hw hh b
  have f := use_log (fun i:I×Points 3=>X i.1 i.2) (fun i:I×Points 3=>fox N i.2 (s i.1) q) cost x (fun b=> aperture N M H s hh b _ )
  have F': Tendsto Prod.fst care F :=tendsto_fst
  have h := (ap_crop N M H s ht hh q).trans (hq.comp_tendsto F')
  have e i : ContinuousOn (fun x=>pie N x (s i) q) (conf 3):=by
    simp_rw [pie,crop_apply]; exact continuousOn_finsetSum _ fun i _=> (Select.steady (W 6) (orders N M H).light).const_mul _
  exact opening (hp0.mono fun i hi=>⟨hi,e i⟩) ((f.add h).congr_left (fun i=>sub_add_sub_cancel ..)) (subset_refl _)
lemma reread (he:1 ≤ q) :
    (fun i=> ((a).applyTo (fun x=>log3 (X i x))).re/Rose.c_T N.criterion - s i)=O[F] w := by
  have h := ((Complex.reCLM.isBigO_comp ..).trans (relog N M H s X cost hw hq ht hh hp0)).const_mul_left (Rose.c_T N.criterion)⁻¹
  refine h.congr_left fun i=>?_ ; change _ * ((_ - (a).applyTo (fun x=>crop q (s i) (Scale.Select.Single (W 6) x))).re) = _; rw [receipt N M H _ he,Complex.sub_re]; simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; field_simp [(show Rose.c_T N.criterion ≠ 0 from N.criterion.fresh.ne)]

omit hw cost hq hh ht hp0 H
lemma continuous_log3 {X: Points 3→Rose.Badge→ℂ} (h:∀s, ContinuousOn (fun x=>X x s) (conf 3)) :
    ContinuousOn (fun x=>log3 (X x)) (conf 3) := by
  unfold log3; exact ((h _).sub ((((h _).mul (h _)).add ((h _).mul (h _))).add ((h _).mul (h _)))).add (continuousOn_const.mul (((h _).mul (h _)).mul (h _)))
include H V hz hp hJ
lemma ledger (he:6≤d) (he':1 ≤ m) : (fun i:ℝ=> Paper.meter U J N.criterion i - t i)=O[late] fun i=>δ i^m := by
  let X i (x:Points 3) b:= FF i 6 3 x (ret G b); have hf : ∀ᶠ i in late, 0 < i := self_mem_nhdsWithin
  exact reread N M H t X (fun b=>six_price U J hJ N A t V hz hp M H he (ret G b)) (isBigO_const_of_tendsto ((g0_zero sim).pow m) one_ne_zero) (Fare.over_pow _ _ (V.enough.trans (Nat.le_succ _)) late (δ) ((g0_zero sim).abs.eventually (ge_mem_nhds (by simp))))
    (candidate_fee N t M H V.calibrated) ((coupling_payment sim V.calibrated).mono fun i hi=> hi.2.1) (hf.mono fun i hi=> continuous_log3 (fun b=> Paper.smooth U J (ret G b) hi)) (he'.trans V.enough)
end YM.FVA2.GradedFar259.Pose
