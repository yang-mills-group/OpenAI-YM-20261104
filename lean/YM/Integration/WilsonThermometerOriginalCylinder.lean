import YM.Integration.WilsonThermometerBareStore
import YM.Integration.WilsonCenteredDetectorUnit
import YM.Integration.ActualWilsonPrimaryPreparation
import YM.Integration.QLocalPhysicalBirthClock

/-! One affordable original-source credential for the complete signed
thermometer on the bare Wilson hierarchy, including all rough fields. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerOriginalCylinder
open Filter Function Finset Set MeasureTheory Lattice Wilson RG Source Labels Marker
open Push.Local FVA1 PhysicalNext.Repeat.Legato Next.Foundations Trace.Pilot
open Next.Rank Next.UVStress RG16.Literal MergeProof.East OriginalForcedAddresses
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading WilsonThermometerCourseIntake WilsonThermometerCenteredAlgebra
open WilsonThermometerWeightedCapture WilsonThermometerLiteralCredit WilsonCenteredFiledAtoms
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (simple : G.Simple)
local notation "C" => R.family
local notation "F" => R.family.labels.level 0
local notation "J" => Stock.census (Fin 3)
local notation "Y" => R.family.params
local notation "S" => R.family.localSection 0
local notation "W" N:max p:max => R.family.path.rep N p N
local notation "κ" N:max => LocalComparison.forcedDivisor R.family N
local notation "μ" N:max p:max => Next.Foundations.price G (max (W N p).p.order (W N p).p.power)

include simple in
theorem original : ∀ᶠ N : ℕ in atTop, ∀ (per : ℕ) (A : Group C 6)
    (o : Positions (Fin 3) (R.family.side N per)) (y : Site (R.family.side N per))
    (Q : Poly J) (rad : ℕ) (_ : ∀ j : Fin 3, separation (o.origin j) y ≤ rad)
    (E : (J).Mode → ℝ) (_ : ∀ s U, ‖WilsonThermometerCourseHot.bare R A o s U‖ ≤ E s),
    let fees := fun s => WilsonThermometerBareStore.fee R A o s y (κ N) (E s) (μ N per) rad
    ∃ q : Coefficient (F) (R.family.side N per),
      q.Format y (Y) (W N per) ∧ q.remBound y (W N per) (κ N) (∑ s, ‖weight Q s‖*fees s) ∧
      (F).coeffSize q.x ≤ testPrice (F)*(∑ s,‖weight Q s‖*E s) ∧
      (∀ U,q.density y (S) (W N per) U=((W N per).eval U:ℂ)*cut R A o Q U) ∧
      credit C N per 0 (cut R A o Q) N le_rfl = q.density y (S) (W N per) := by
  have warm := (tendsto_order.mp (QLocalPhysicalBirthClock.late_forcing simple (C).path.levels)).2 1 zero_lt_one
  filter_upwards [warm,eventually_ge_atTop ((C).ref 0),
    eventually_all.mpr (fun j : Fin 3=>eventually_ge_atTop ((C).ref (grade j)))] with N room enrolled refs
  intro per A o y Q rad near E cap fees
  let P := W N per
  have paid := R.makes.wilson.represents N per N (le_refl N)
  have read := ActualWilsonPrimaryPreparation.original R 0 N per N enrolled le_rfl
  have hk : 0 < κ N := Real.sqrt_pos.mpr (Real.exp_pos _)
  have fieldRoom : hitWidth P.p*(C).path.levels.clock.forcedAllowance N ≤ 1 := by
    have shape : P.p=(C).path.levels.budget N := paid.vac
    rw [shape];exact room.le
  choose H formats bills raw using fun s : (J).Mode=>
    WilsonThermometerBareStore.offered R A simple o s y refs rad (fun j _=>near j) hk fieldRoom read (cap s)
  have born (s : (J).Mode) (U : Config G (R.family.side N per)) :
      (incoming R A simple (le_refl N) o U).part s= (P.eval U:ℂ)*WilsonThermometerCourseHot.bare R A o s U := by
    rw [incoming,WilsonPositionThermometerDepositedFaces.deposited R simple N per A.station
      (fun j : Fin 3=>index A (grade j)) (vector A univ) o refs le_rfl s U,
      actualTransport_base C R.makes le_rfl,Complex.real_smul]
    rfl
  obtain ⟨form,remains,-,-,whole⟩:=deposited R A simple (le_refl N) o P y H Q hk paid.good fees
    formats bills (fun s U=>(raw s U).trans (born s U).symm)
  let q:=assembled H Q
  have density (U : Config G (R.family.side N per)) :
      q.density y (S) P U=(P.eval U:ℂ)*cut R A o Q U := by
    rw [whole,WilsonThermometerCenteredAlgebra.affine,WilsonThermometerLiteralCredit.cut,Finset.sum_apply,mul_sum]
    apply sum_congr rfl
    intro s _
    rw [born,Pi.smul_apply,smul_eq_mul]
    ring
  let readPrice : ℝ := ∑ s : (J).Mode, ‖weight Q s‖*E s
  have each : ‖cut R A o Q 1‖ ≤ readPrice := by
    rw [WilsonThermometerLiteralCredit.cut,Finset.sum_apply]
    exact (norm_sum_le ..).trans (sum_le_sum fun s _=>by
      rw [Pi.smul_apply,norm_smul]
      exact mul_le_mul_of_nonneg_left (cap s 1) (norm_nonneg _))
  have nz : (P.eval (1 : Config G (R.family.side N per)):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Multi.AxisShift.chosen_positive R.makes.wilson (p:=per) (le_refl N) _).ne'
  have sense : (F).coeffSize q.x ≤ testPrice (F)*readPrice := by
    apply (probe_budget (F)).choose_spec.choose_spec.2 _ _ ((norm_nonneg _).trans each)
    intro p _
    have grade0 : p.2.val=0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ p.2.isLt)
    rw [WilsonCenteredDetectorUnit.flatProbe q form read.sound p grade0,density,←mul_assoc,inv_mul_cancel₀ nz,one_mul]
    exact each
  exact ⟨q,form,remains,sense,density,(WilsonThermometerLiteralCredit.returned R A simple o Q refs le_rfl).trans
    (funext whole).symm⟩

end YM.Integration.WilsonThermometerOriginalCylinder
