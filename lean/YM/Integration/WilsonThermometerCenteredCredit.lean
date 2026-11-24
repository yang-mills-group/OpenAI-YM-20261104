import YM.Integration.WilsonThermometerCenteredAlgebra
import YM.Integration.WilsonThermometerUnitFilingReturn
import YM.Integration.IntrinsicProductLinearity

/-! The same complete three-field cylinder before every intervening Wilson
push, with its ordinary reference inverse filed independently of the field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCenteredCredit
open Filter Function Set MeasureTheory Table Spec Lattice Wilson RG Source Marker Extraction Climb Trace.Pilot
open Next.UVStress Next.Rank RG12 RG17 PhysMS PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent MergeProof.East
open FVA1 OriginalForcedAddresses XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox
open RG16.Literal WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading WilsonThermometerCourseIntake WilsonThermometerCenteredAlgebra
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple)
local notation "J" => Stock.census (Fin 3)
local notation "C" => R.family

def source (z : UVIndex) (o : Positions (Fin 3) (R.family.side z.1 z.2)) (Q : Poly J) :
    Cut C z.1 z.2 := ∑ s : (J).Mode, weight Q s • placed R A z s.val o.origin

def table (z : UVIndex) (o : Positions (Fin 3) (R.family.side z.1 z.2)) : Poly J :=
  Poly.inject fun s => row A z o.origin s.val

private theorem smooth (z : UVIndex) (o : Positions (Fin 3) (R.family.side z.1 z.2)) (s : (J).Mode) :
    Continuous (placed R A z s.val o.origin) := by
  apply continuous_finsetProd
  intro i _
  exact R.family.continuousO z.1 z.2 _ _ _

theorem continuous_source (z : UVIndex) (o : Positions (Fin 3) (R.family.side z.1 z.2)) (Q : Poly J) :
    Continuous (source R A z o Q) := by
  unfold source
  rw [show (∑ s : (J).Mode, weight Q s • placed R A z s.val o.origin)=_ from
    funext (fun U => Finset.sum_apply U _ _)]
  exact continuous_finsetSum _ fun s _ => (smooth R A z o s).const_smul (weight Q s)

theorem deposited {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}
    (checked : A.station.checked f H A.horizon)
    (unit : ∀ t : Fin 7, A.change t ((Bel R.family.book).unit t)=(Bel R.family.book).unit t) :
    ∀ᶠ z : UVIndex in f.fuse, ∀ k (upper : k≤z.1)
      (o : Positions (Fin 3) (R.family.side z.1 z.2)) (Q : Poly J),
      credit C z.1 z.2 0 (source R A z o Q) k upper =
        fun U => (total (incoming R A simple upper o U) Q).part full := by
  filter_upwards [WilsonThermometerUnitFilingReturn.density R A simple checked unit] with z each k upper o Q
  rw [source,IntrinsicProductLinearity.credit_sum C z.1 z.2 0 k upper (weight Q)
    (fun s : (J).Mode => placed R A z s.val o.origin) (smooth R A z o)]
  funext U
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,affine]
  exact Finset.sum_congr rfl fun s _ => congrArg (weight Q s * ·) (congrFun (each k upper o s) U).symm

def normalized (z : UVIndex) {k : ℕ} (upper : k≤z.1)
    (o : Positions (Fin 3) (R.family.side z.1 z.2)) (Q : Poly J) : ℂ :=
  (∫ U, credit C z.1 z.2 0 (source R A z o Q) k upper U ∂prior G (R.family.side k z.2)) /
    (∫ U, ((R.family.path.rep z.1 z.2 k).eval U : ℂ) ∂prior G (R.family.side k z.2))

include simple in
theorem heard {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}
    (checked : A.station.checked f H A.horizon)
    (unit : ∀ t : Fin 7, A.change t ((Bel R.family.book).unit t)=(Bel R.family.book).unit t) :
    ∀ᶠ z : UVIndex in f.fuse, ∀ k (upper : k≤z.1)
      (o : Positions (Fin 3) (R.family.side z.1 z.2)) (Q : Poly J),
      normalized R A z upper o Q=(total (table R A z o) Q).part full := by
  filter_upwards [deposited R A simple checked unit,
    WilsonThermometerUnitFilingReturn.original R A simple checked unit,
    WilsonThermometerUnitFilingReturn.density R A simple checked unit] with z invoice rows each k upper o Q
  have summable (s : (J).Mode) : Integrable (fun U => weight Q s*(incoming R A simple upper o U).part s)
      (prior G (R.family.side k z.2)) := by
    have int := credit_int C z.1 z.2 0 _ (smooth R A z o s) upper
    rw [← each k upper o s] at int
    exact int.const_mul _
  rw [normalized,invoice k upper o Q]
  simp_rw [WilsonThermometerCenteredAlgebra.affine]
  rw [integral_finsetSum Finset.univ (fun s _ => summable s),Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_const_mul,mul_div_assoc]
  exact congrArg (weight Q s * ·) (rows k upper o s)

theorem unit_table {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}
    (checked : A.station.checked f H A.horizon)
    (unit : ∀ t : Fin 7, A.change t ((Bel R.family.book).unit t)=(Bel R.family.book).unit t) :
    ∀ᶠ z : UVIndex in f.fuse, ∀ (o : Positions (Fin 3) (R.family.side z.1 z.2)),
      (table R A z o).part (J).quiet=1 := by
  filter_upwards [subwords R A checked unit] with z words o
  change R.family.omega z.1 z.2 (placed R A z ∅ o.origin)=1
  rw [show placed R A z ∅ o.origin=fun _ => (1:ℂ) from by funext U; simpa using words ∅ o.origin U]
  simp [Family.omega,Wilson.moment]

end YM.Integration.WilsonThermometerCenteredCredit
