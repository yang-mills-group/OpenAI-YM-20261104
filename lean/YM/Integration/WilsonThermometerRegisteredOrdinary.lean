import YM.Integration.WilsonThermometerRegisteredPair
import YM.Integration.WilsonOriginalThermometerReportedFaces
import YM.Integration.WilsonThermometerCourseResidual
import YM.Integration.WilsonReceivedCenteredMoment

/-! The ordinary two-field detector after blocking twice, with the two actual singleton means. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerRegisteredOrdinary
open Filter Finset Lattice Wilson RG Source Labels Marker QuadraticLocal QuadraticLocal.Earn FVA1 Cells MeasureTheory
open Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent MergeProof.East OriginalForcedAddresses Extra.Trajectories
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonThermometerCourseIntake
open Comparison.RG02 Comparison.RG02.Cumulants Comparison.RG02.Order FVA1Physical.Round2.CP5
open WilsonThermometerCourseHearing WilsonLimitConstruction
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6)
    {N per i:ℕ} (live:i < N) (o:Positions (Fin 3) (R.family.side N per))
local notation "J" => Stock.census (Fin 3)

/-- The two-field numerator is normalized by the whole unmarked law on its actual date. -/
def conditional (t:Fin 3) (W:Config G (R.family.side i per)) : Poly J :=
  (((R.family.path.rep N per i).eval W:ℂ)⁻¹) •
  LocalComparison.actualPush R.family N per i
    (offered R A simple live o (WilsonThermometerRegisteredPair.without t)) W

/-- Every surviving face is its true normalized conditional Wilson moment, including
the old joint deposit and all of the original compulsory branches. -/
theorem observed (pos:0 < i) (refs:∀ v,R.family.ref (grade v) ≤ N) (t:Fin 3)
    (W:Config G (R.family.side i per)) (s:(J).Mode) :
    (conditional R simple A live o t W).part s =
    if t∈s.val then 0 else
      (WilsonThermometerCourseResidual.table R A simple live.le o W).part s := by
  cases i with
  | zero => omega
  | succ j =>
    have moved:=congrFun (congrFun (WilsonThermometerTestedReturn.push R A simple live o refs)
      (WilsonThermometerRegisteredPair.without t)) W
    unfold conditional
    rw [moved,Poly.part_smul,WilsonThermometerRegisteredPair.face]
    by_cases own:t∈s.val <;>
      simp [own,WilsonThermometerCourseResidual.table,Poly.part_smul]

theorem quiet (pos:0 < i) (refs:∀ v,R.family.ref (grade v) ≤ N) (t:Fin 3)
    (W:Config G (R.family.side i per)) :
    (conditional R simple A live o t W).part (J).quiet = 1 := by
  rw [observed R simple A live o pos refs t W]
  rw [if_neg (show t∉(J).quiet.val from notMem_empty _),
    WilsonThermometerCourseResidual.observed R A simple live.le o refs W]
  change actualTransport R.family (N:=N) (fun U => ∏ v ∈ (∅:Finset (Fin 3)), _) live.le W = 1
  simpa only [prod_empty ] using actualTransport_const R.family R.makes le_rfl (1:ℂ) live.le W

variable {f:Extraction.Order} {F:(Bel R.family.book).Hierarchy} {δ:ℝ} {T:Campaign R}
    {V:Campaign.Pillars R T} (fund:FundedOriginalProperties.{u} simple δ V)
    (slow:WilsonWindowReportingPace.Slow R.kit)

def gross : ℝ := (WilsonOriginalThermometerReportedFaces.leg R (f:=f) (H:=F) simple fund slow).choose
def power : ℕ := (WilsonOriginalThermometerReportedFaces.leg R (f:=f) (H:=F) simple fund slow).choose_spec.2.choose
def opening : ℕ := (eventually_atTop.mp (WilsonOriginalThermometerReportedFaces.leg R (f:=f) (H:=F)
  simple fund slow).choose_spec.2.choose_spec).choose

/-- Bounds on the two physical singleton cofactors at every retained older field.
The exponent and date precede the period, tests and choices of the two positions. -/
theorem singleton (late:opening R simple (f:=f) (F:=F) fund slow ≤ i) (pos:0 < i)
    (date:A.station.k=i) (checked:A.station.checked f F A.horizon)
    (near:WilsonOriginalThermometerMicroscopic.close R A)
    (o:Positions (Fin 3) (R.family.side (i+2) per))
    (refs:∀ v,R.family.ref (grade v) ≤ i+2) (t v:Fin 3) (W:Config G (R.family.side i per)) :
    ‖(conditional R simple A (by omega : i < i+2) o t W).part ((J).fire v)‖ ≤
      gross R simple (f:=f) (F:=F) fund slow * (R.family.path.levels.clock.hatBeta i)^
        (power R simple (f:=f) (F:=F) fund slow) := by
  let K := gross R simple (f:=f) (F:=F) fund slow
  let e := power R simple (f:=f) (F:=F) fund slow
  have K₁ : 1 ≤ K := (WilsonOriginalThermometerReportedFaces.leg R (f:=f) (H:=F) simple fund slow).choose_spec.1
  have price:=(eventually_atTop.mp (WilsonOriginalThermometerReportedFaces.leg R (f:=f) (H:=F)
    simple fund slow).choose_spec.2.choose_spec).choose_spec i late A date checked near per v (o.origin v)
  rw [observed R simple A _ o pos refs t W]
  split_ifs
  · rw [norm_zero]
    exact mul_nonneg (zero_le_one.trans K₁) (pow_nonneg (zero_le_one.trans ((R.family.path.levels.fits.delayed i).le)) _)
  · rw [WilsonThermometerCourseResidual.observed R A simple (by omega : i ≤ i+2) o refs W]
    change ‖actualTransport R.family (N:=i+2) (fun U=> ∏ v∈({v}:Finset (Fin 3)), _)
      (by omega : i ≤ i+2) W‖ ≤ _
    simpa only [prod_singleton,gross,power] using actualTransport_norm_le R.family R.makes (le_refl (i+2)) price (by omega : i ≤ i+2) W

/-- Reading an ordinary pair from the complete second-block signed logarithm retains
the two physical singleton means. The report currency is applied before taking norms. -/
theorem pair (Y Z:Poly J) (w:Fin 3→ℝ) (hw:∀v,0<w v) (unit:Y.part (J).quiet=1)
    {E C:ℝ} (change:Poly.price w (Order.logTo 3 Y-Z) ≤ E)
    (a b:Fin 3) (s:(J).Mode) (ab:a≠b) (face:s.val={a,b})
    (left:w a*‖Y.part ((J).fire a)‖ ≤ C) (right:w b*‖Y.part ((J).fire b)‖ ≤ C) :
    Poly.toll w s*‖Y.part s-(Z.part s+Z.part ((J).fire a)*Z.part ((J).fire b))‖ ≤ E*(1+2*C+E) := by
  let dx:=fun h:(J).Mode=>((connected Y).part h-Z.part h)
  have read : connected Y = Order.logTo 3 Y :=
    Order.log_to Y unit 3 (fun h => by simpa only [Fintype.card_fin ] using card_le_univ h.val)
  have paid (h:(J).Mode) : Poly.toll w h*‖dx h‖ ≤ E := by
    change Poly.toll w h*‖(connected Y-Z).part h‖ ≤ E
    rw [read];exact (Poly.member hw h _).trans change
  let A:=(J).fire a
  let B:=(J).fire b
  have sa: Poly.toll w A=w a := by simp [A,Poly.toll,Census.fire]
  have sb: Poly.toll w B=w b := by simp [B,Poly.toll,Census.fire]
  have sn: Poly.toll w s=w a*w b := by simp [Poly.toll,face,ab]
  have pa:w a*‖dx A‖ ≤ E := by simpa only [sa ] using paid A
  have pb:w b*‖dx B‖ ≤ E := by simpa only [sb ] using paid B
  have headA: (connected Y).part A=Y.part A:=lamp a Y unit
  have headB: (connected Y).part B=Y.part B:=lamp b Y unit
  have za:w a*‖Z.part A‖ ≤ C+E:=calc
    _ ≤ w a*(‖Y.part A‖+‖dx A‖):= by
      apply mul_le_mul_of_nonneg_left _ (hw a).le
      rw [show Z.part A=Y.part A-dx A by dsimp [dx];rw [headA];ring]
      exact norm_sub_le _ _
    _ ≤ _ := by rw [mul_add]; exact add_le_add left pa
  have exactPair : Y.part s-(Z.part s+Z.part A*Z.part B) =
      dx s+dx A*Y.part B+Z.part A*dx B := by
    dsimp [dx]
    rw [twins a b s Y unit ab face,headA,headB]
    ring
  have weighted : Poly.toll w s*‖dx A*Y.part B‖ ≤ E*C := by
    rw [sn,norm_mul]
    calc
      _ = (w a*‖dx A‖)*(w b*‖Y.part B‖) := by ring
      _ ≤ _ := mul_le_mul pa right (mul_nonneg (hw b).le (norm_nonneg _))
        ((mul_nonneg (hw a).le (norm_nonneg _)).trans pa)
  have other : Poly.toll w s*‖Z.part A*dx B‖ ≤ (C+E)*E := by
    rw [sn,norm_mul]
    calc
      _ = (w a*‖Z.part A‖)*(w b*‖dx B‖) := by ring
      _ ≤ _ := mul_le_mul za pb (mul_nonneg (hw b).le (norm_nonneg _))
        ((mul_nonneg (hw a).le (norm_nonneg _)).trans za)
  rw [show Y.part s-(Z.part s+Z.part ((J).fire a)*Z.part ((J).fire b))=_ from exactPair]
  have triangle:= (norm_add_le (dx s+dx A*Y.part B) (Z.part A*dx B)).trans
    (add_le_add (norm_add_le (dx s) (dx A*Y.part B)) (le_refl _))
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left triangle (Poly.worth hw s).le
    _ = _ := by rw [mul_add,mul_add]
    _ ≤ _ := add_le_add (add_le_add (paid s) weighted) other
    _ = _ := by ring

end YM.Integration.WilsonThermometerRegisteredOrdinary
