import YangMills.WilsonProof.NativeSupport.Commissioned259.Pose.Affair
/-!
# Upward t pricing & powers on compact W reports

Prove parts of BB F.3 and F.4 on these continuum purchases. `C5` is a strong assumption on U
and positions in W, for its own finite purposes (not claiming establishment). See README.
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

variable {I:Type*} {F:Filter I} {E' : Type*} [Norm E']
    {G : Gauge} {d n q m e : ℕ} {C : Family G} {f : Extraction.Order} {S : Table C.book}
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
local notation "τ" => Paper.meter U J N.criterion

variable {w'I s v g : I→ℝ} {z:I→PowerSeries ℂ}
lemma move_cost (hv : v=O[F] home) (hs : s=O[F] home) (h : (fun i=> s i-v i)=O[F] g)
    (hz : Tunes home F w'I z) (p : ℕ) : (fun i=> crop p (s i) (z i)-crop p (v i) (z i))=O[F] fun i=> g i * w'I i := by
  have H : ∀ p:ℕ,(fun i=>s i^p-v i^p)=O[F] g := by
    intro p; induction p with
    | zero=> simp_rw [pow_zero,sub_self]; exact isBigO_zero ..
    | succ n ih=>
      have hf := (hs.pow n).congr_right (g₂:=home) fun i=>one_pow _
      refine (((ih.mul hv|>.congr_right (fun i=>mul_one _))).add (hf.mul h|>.congr_right (fun i=>one_mul _))).congr_left fun i=>?_; rw [pow_succ,pow_succ]; ring
  simp_rw [crop_apply, ← Finset.sum_sub_distrib,←sub_mul,← Complex.ofReal_pow, ← Complex.ofReal_sub]
  exact IsBigO.sum (fun i hi=> ((Complex.ofRealCLM.isBigO_comp ..).trans (H i)).mul (homebound (hz i)))
include hJ hp H
include V hz
lemma calibration (he : 6 ≤ d) (hm : 2 ≤ m) : Calibrated G τ :=
  poseFit_calibrates sim 0 V.calibrated ((ledger U J hJ N A t V hz hp M H he (by omega)).trans (Fare.over_pow 2 m hm late (δ) ((g0_zero sim).abs.eventually (ge_mem_nhds (by simp)))))
lemma committed (he : 6 ≤ d) (hm : 2 ≤ m) (p : ℕ) (hh : p+1 ≤ m) {R:Alcove} (hR:R∈S0) (u:Tags G d R.n) :
    (fun i:ℝ×Points R.n=> FF i.1 d R.n i.2 u - array (W d) i.2 p (τ i.1) u)=O[booth R.K late] fun i=>δ i.1^(p+1) := by
  let L:= booth R.K late; have x:Tendsto Prod.fst L late := tendsto_fst
  obtain hk:= bare_price U J N A t V hz hp M H hR u
  have h := ((isBigO_neg_left.mpr (ledger U J hJ N A t V hz hp M H he (by omega))).comp_tendsto x).congr_left
    (f₂:=fun i=>t i.1-τ i.1) fun i=>by dsimp only [Function.comp_apply]; rw [neg_sub]
  have hτ:= (candidate_fee N τ M H (calibration U J hJ N A t V hz hp M H he hm)).comp_tendsto x
  have g0 := isBigO_const_of_tendsto ((g0_zero sim).comp x) (show (1:ℝ)≠0 from one_ne_zero)
  have P : (fun i:ℝ×Points R.n=> array (W d) i.2 q (t i.1) u - array (W d) i.2 q (τ i.1) u)=O[L] fun i=>δ i.1^m := by
    simp_rw [array_eq]; exact (move_cost (hτ.trans g0) (((candidate_fee N t M H V.calibrated).comp_tendsto x).trans g0) h (compact_tunes (W d) (orders N M H).light R.cost R.space placed u) q).congr_right fun i=> mul_one _
  have hp := x.eventually ((coupling_payment sim (calibration U J hJ N A t V hz hp M H he hm)).mono fun i hi=>hi.2.1)
  exact ((((hk.add P).congr_left (fun i=> sub_add_sub_cancel ..)).trans ((Fare.over_pow _ _ hh late (δ) ((g0_zero sim).abs.eventually (ge_mem_nhds (by simp)))).comp_tendsto x)).add (truncate_array _ (orders N M H).light R.cost R.space placed u hτ _ _ hp ((le_of_lt hh).trans V.enough) )).congr_left (fun i=> sub_add_sub_cancel ..)

omit V hz
-- no need uniform prices over arbitrary arities OR a SINGLE choice of q over all
-- Alcoves. Global fixed coupons *not* required for summary tasks. But C5 purchases
-- on joint tasks need all with ONE t' and calibration maps. `m` exponent, up to q.
-- taking aggregate for ALL compacts only for COMPARISON other than main M2 bound.
def Shop (U : Final C f S) (J : ℝ→tower S) (N : WilsonPrescription G) : Prop :=
    ∀ (d : ℕ) (_:6≤d), ∀ m:ℕ, 2 ≤ m → ∀ S:Finset Alcove, ∃ (t:ℝ→ℝ)(A:ℝ→Change G d)(q:ℕ), C5 U J N A t S m q
variable (L : Shop U J N)
include L
lemma guaranteed : Calibrated G τ := by
  obtain ⟨t,A,q,V⟩:= L 6 le_rfl 2 le_rfl (requests N 6); exact calibration U J hJ N A t V subset_rfl hp M H le_rfl le_rfl
lemma F4 (R : Alcove) (v : Tags G d R.n) (p:ℕ) :
    (fun i:ℝ×Points R.n=> FF i.1 d R.n i.2 v - array (W d) i.2 p (τ i.1) v) =O[booth R.K late] fun i=>δ i.1^(p+1) := by
  let e:= max 6 d; have he : d ≤ e:= le_max_right ..
  let S0 := insert R (requests N e); obtain ⟨t,A,q,V⟩ := L e (le_max_left ..) (p+2) (by omega) S0
  apply (committed U J hJ N A t V (Finset.subset_insert ..) hp M H (le_max_left ..) (by omega) p (by omega) (Finset.mem_insert_self ..) (up he ∘ v)).congr' ?_ (EventuallyEq.refl ..)
  filter_upwards [tendsto_fst.eventually (Paper.pointing U J hJ (n:=R.n) he), placed] with i hi hj
  rw [array_rises N M H he (R.space hj) v,hi v _ (R.space hj)]
  rfl
end YM.FVA2.GradedFar259.Pose
