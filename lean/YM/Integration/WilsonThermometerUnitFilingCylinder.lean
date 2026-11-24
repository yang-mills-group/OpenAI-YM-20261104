import YM.Integration.WilsonThermometerUnitFilingHearing
import YM.Integration.WilsonThermometerCourseIntake
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Algebra

/-! The complete measured three-field source, with its placement-dependent
independent inverse and its actual three fine cell coordinates. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCylinder
open Function Set Filter MeasureTheory Finset Lattice Wilson RG Source Labels Table Spec XSpace XSpace.Rose
open Extraction Climb Next.UVStress RG12 RG17 PhysicalNext.Repeat.Legato
open Bid RG16 RG16.Literal Trace.Physical.GermGraph MergeProof MergeProof.Accent FVA1 Marker
open WilsonPositionThermometerCapStation WilsonThermometerCourseIntake WilsonThermometerUnitFilingFeed
open Primitives.GCC.Anchor
open scoped BigOperators Topology Classical
variable {G : Gauge} (R : Run G) (A : Group R.family 6)
local notation "J!" => Stock.census (Fin 3)
abbrev Sites (z : UVIndex) := Fin 3 → Site (R.family.side z.1 z.2)

/-- This is the complementary coefficient of the independent squarefree inverse,
fixed at the placement before the Wilson variable is read. -/
def wallet (Q : Poly J!) (s : (J!).Mode) : ℂ :=
  (inverseMass Q).part ⟨univ \ s.val,mem_univ _⟩

def source (z : UVIndex) (y : Sites R z) (Q : Poly J!) : Cut R.family z.1 z.2 :=
  ∑s : (J!).Mode,wallet Q s • placed R A z s.val y

def cylinder (z : UVIndex) (r : ℝ) (φ : Test 3) (Q : Sites R z→Poly J!) : Cut R.family z.1 z.2 :=
  let χ := WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z
  ∑y,WilsonSeparatedOriginalThermometerCells.weight φ χ y • source R A z y (Q y)

private theorem smooth_face (z : UVIndex) (y : Sites R z) (s : (J!).Mode) :
    Continuous (placed R A z s.val y) := by
  apply continuous_finsetProd
  intro j _
  exact R.family.continuousO z.1 z.2 _ _ _

private theorem smooth_sum {I : Type} [Fintype I] (z : UVIndex) (w : I→ℂ) (u : I→Cut R.family z.1 z.2)
    (hu : ∀i, Continuous (u i)) : Continuous (∑i,w i • u i) := by
  rw [show (∑i,w i • u i)=_ from funext (fun U => Finset.sum_apply U _ _)]
  exact continuous_finsetSum _ fun i _ => (hu i).const_smul _

theorem continuous_cylinder (z : UVIndex) (r : ℝ) (φ : Test 3) (Q : Sites R z→Poly J!) :
    Continuous (cylinder R A z r φ Q) := by
  apply smooth_sum
  intro y
  exact smooth_sum R z _ _ (smooth_face R A z y)

private theorem linear_mean {I : Type} [Fintype I] (z : UVIndex) (w : I→ℂ) (u : I→ Cut R.family z.1 z.2)
    (hu : ∀i, Continuous (u i)) :
    R.family.omega z.1 z.2 (∑i,w i • u i)=∑i,w i*R.family.omega z.1 z.2 (u i) := by
  unfold Family.omega moment
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun _ _=>integral_const_mul _ _
  · exact fun i _=> ((hu i).const_mul (w i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def tested (z : UVIndex) (r : ℝ) (φ : Test 3) (Q : Sites R z→Poly J!) : ℂ :=
  let χ := WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z
  φ.applyTo fun x=>∑s : (J!).Mode,wallet (Q (χ x)) s *
    WilsonPositionThermometerGradedReading.row A z (χ x) s.val

/-- All Wilson faces at the independent microscopic displacements are heard
against their common original normalized law. -/
theorem literal (z : UVIndex) (r : ℝ) (φ : Test 3) (Q : Sites R z→Poly J!) :
    R.family.omega z.1 z.2 (cylinder R A z r φ Q)=tested R A z r φ Q := by
  unfold tested cylinder
  rw [WilsonSeparatedOriginalThermometerCells.tested φ _ (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r z)
    (fun y=>∑s : (J!).Mode,wallet (Q y) s * WilsonPositionThermometerGradedReading.row A z y s.val)]
  dsimp only
  rw [linear_mean R z (WilsonSeparatedOriginalThermometerCells.weight φ (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z))
    (fun y=>source R A z y (Q y)) (fun y=>smooth_sum R z _ _ (smooth_face R A z y))]
  apply Finset.sum_congr rfl
  intro y _
  rw [source,linear_mean R z _ _ (smooth_face R A z y)]
  rfl

/-- The original settlement on this signed cylinder hears a single fixed-date
scalar at every regulator pair. -/
theorem filed (simple : G.Simple) (z : UVIndex) (r : ℝ) (φ : Test 3)
    (Q : Sites R z→Poly J!) {b t J : ℕ} (jt : J≤t) (tb : t≤b) (bN : b≤z.1)
    (ot : Opened R.family 0 t z.2) (B : R.family.label 0) (q : store R.family 0 z.2 b) {E dR w : ℝ}
    (fund : Funds R.family R.makes z.2 z.1 b 0 J t E dR w (cylinder R A z r φ Q) jt tb bN ot B q) :
    ‖tested R A z r φ Q-report R (cylinder R A z r φ Q) t‖ ≤ 2*(stakes R.family J t/w)+E/gainChart R.family.path b t := by
  rw [←literal R A z r φ Q]
  exact WilsonThermometerUnitFilingHearing.original R simple jt tb bN ot _ (continuous_cylinder R A z r φ Q) B q fund

end YM.Integration.WilsonThermometerUnitFilingCylinder
