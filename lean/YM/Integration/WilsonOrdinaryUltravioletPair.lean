import YM.Integration.WilsonPhysicalMarkedDefectPhysicalHistory
import YM.Integration.WilsonFactoryBoxedFields
import YM.Integration.WilsonOrdinaryCombinedSource

/-! Exact complete two-slot upper source in the original canopy's canonical
marks. The coefficients keep the lattice spacing and inverse terminal chart. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryUltravioletPair
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces Extra.Iteration Extra.Histories
open Integration.LocalComparison VowsR QuadraticLocal.Mentor QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore Marker QuadraticLocal.Tint QuadraticLocal.Syl RG3.Annuncia
open Next.Foundations FVA1Physical.Round2.Curvature FVA1Physical.Round2.CP5 FVA1Physical.MixedResets
open scoped Classical BigOperators

open Function Finset Lattice Wilson Labels PertExtension PertExtension.LatticePT
open Pert Pert.Position Maxwell Maxwell.Free PositionX PositionX.Bare.Shop PositionX.Bare.Subcell
open RG PhysicalNext.Repeat.Legato MS MS.Koszul MS.Theater MS.Book MS.Book.Program MS.Book.Convolve
open MS.Land MS.Menus FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open FormalOPE.RG10.MultiGauge FormalOPE.RG10.InversionTop FVA2 FVAAlt2
open FVA2.Clock FVA2.Score FVA2.Based FVA2.PairCoords FVA2.Modes FVA2.Paper FVA2.Trans FVA2.ColorCode FVA2.Attend
open RegulatorIR.FVAAlt2.Lodge Extra.Histories
open scoped Classical BigOperators

open WilsonPhysicalMarkedDefect WilsonFactoryBoxedFields MeasureTheory Filter
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G)

/-- The authentic terminal basis member, at the actual ambient engineering cutoff. -/
def seat (d : ℕ) (q : (R.family.labels.level d).Index) : CoverLabel G d :=
  ⟨⟨d,Nat.lt_succ_self d⟩,q⟩

theorem grade (d : ℕ) (q : (R.family.labels.level d).Index) :
    nativeGrade (seat R d q) = ((R.family.labels.level d).grades q).2 := rfl

/-- The full physical coefficient of the normalized enrolled insertion. -/
def coefficient (d N per : ℕ) (v : R.family.label d) (g : ℝ)
    (q : (R.family.labels.level d).Index) : ℂ :=
  ((R.family.S.a N : ℂ)^d)⁻¹ * WilsonFactoryBoxedFields.restored R d N per v g q

/-- This is precisely the singleton field at the head of the native
`bought_history`, with its native grade and its honest unsmeared site. -/
def enrolled (d N per : ℕ) (g : ℝ) (q : (R.family.labels.level d).Index)
    (x : Site (R.family.side N per)) (U : Config G (R.family.side N per)) : ℂ :=
  ((g^(nativeGrade (seat R d q)))⁻¹ : ℝ) •
    (R.family.localSection (seat R d q).1.val).places (Pi.single (seat R d q).2 1) x U

/-- A definite physical source decomposes in enrolled marks, on every group field. -/
theorem singleton (d N per : ℕ) (v : R.family.label d) {g : ℝ} (hg : g≠0)
    (x : Site (R.family.side N per)) (U : Config G (R.family.side N per)) :
    R.family.O N per v x U = ∑ q,coefficient R d N per v g q * enrolled R d N per g q x U := by
  rw [WilsonFactoryBoxedFields.field R d N per v hg x U]
  unfold WilsonFactoryBoxedFields.word
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  change _ = (_*_)*(((g^(((R.family.labels.level d).grades q).2))⁻¹:ℝ) •
      (R.family.localSection d).places (Pi.single q 1) x U)
  rw [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow]
  change _ = (_*_)*(_*WilsonFactoryBoxedFields.bareRead R d N per q x U)
  ring

/-- The full genuine two-field numerator on the *same* upper configuration,
including its authentic bare Wilson weight, uses the honest pair of enrolled
marks. No product of separately averaged histories occurs. -/
private theorem each (d h N per : ℕ) (v : R.family.label d) (w : R.family.label h)
    {g : ℝ} (hg : g≠0) (x y : Site (R.family.side N per)) (U : Config G (R.family.side N per)) (c : ℂ) :
    c * (R.family.O N per v x U*R.family.O N per w y U) =
    ∑ q,∑ t, (coefficient R d N per v g q * coefficient R h N per w g t) *
      (c * (enrolled R d N per g q x U*enrolled R h N per g t y U)) := by
  rw [singleton R d N per v hg x U,singleton R h N per w hg y U,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- The common original positive Wilson vacuum on both genuine entering marks. -/
theorem joint (d h N per : ℕ) (v : R.family.label d) (w : R.family.label h)
    {g : ℝ} (hg : g≠0) (x y : Site (R.family.side N per)) (U : Config G (R.family.side N per)) :
    (Wilson.bare (R.family.beta N per) U:ℂ) * (R.family.O N per v x U*R.family.O N per w y U) =
    ∑ q,∑ t, (coefficient R d N per v g q * coefficient R h N per w g t) *
      ((Wilson.bare (R.family.beta N per) U:ℂ) * (enrolled R d N per g q x U*enrolled R h N per g t y U)) :=
  each R d h N per v w hg x y U _

private theorem continuous_enrolled (d N per : ℕ) (g : ℝ) (q : (R.family.labels.level d).Index)
    (x : Site (R.family.side N per)) : Continuous (enrolled R d N per g q x) := by
  change Continuous (fun U=>((g^(nativeGrade (seat R d q)))⁻¹:ℝ) • (R.family.localSection d).places (Pi.single q 1) x U)
  exact (continuous_const (y:=((g^(nativeGrade (seat R d q)))⁻¹:ℝ))).smul ((R.family.localSection d).continuous_places (Pi.single q 1) x)

/-- Their integrated value is the same finite signed sum of the original
*two-slot* normalized moments on this very Wilson probability law. -/
theorem measured (d h N per : ℕ) (v : R.family.label d) (w : R.family.label h)
    {g : ℝ} (hg : g≠0) (x y : Site (R.family.side N per)) :
    Wilson.moment (R.family.beta N per) (fun U=>R.family.O N per v x U*R.family.O N per w y U) =
    ∑ q,∑ t,(coefficient R d N per v g q * coefficient R h N per w g t) *
      Wilson.moment (R.family.beta N per) (fun U=>enrolled R d N per g q x U*enrolled R h N per g t y U) := by
  classical
  let c q t := coefficient R d N per v g q * coefficient R h N per w g t
  let f q t := fun U=>enrolled R d N per g q x U*enrolled R h N per g t y U
  let μ := Wilson.law G (R.family.side N per) (R.family.beta N per)
  have cont q t : Continuous (f q t) := (continuous_enrolled R d N per g q x).mul (continuous_enrolled R h N per g t y)
  have row q : Continuous (fun U=>∑t,c q t*f q t U) :=
    continuous_finsetSum _ (fun t _=>continuous_const.mul (cont q t))
  change (∫ U,R.family.O N per v x U*R.family.O N per w y U ∂μ) =
    ∑q,∑t,c q t*(∫ U,f q t U ∂μ)
  calc
    _ = ∫ U,∑q,∑t,c q t*f q t U ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with U
      simpa only [one_mul] using each R d h N per v w hg x y U 1
    _ = _ := by
      rw [MeasureTheory.integral_finsetSum _ (fun q _=>Wilson.continuous_integrable _ (row q))]
      apply Finset.sum_congr rfl
      intro q _
      calc
        _ = ∑t,(∫ U,c q t*f q t U ∂μ) :=
          MeasureTheory.integral_finsetSum _ (fun t _=>((Wilson.continuous_integrable _ (cont q t)).const_mul (c q t)))
        _ = _ := by
          apply Finset.sum_congr rfl
          intro t _
          exact MeasureTheory.integral_const_mul (c q t) _

/-- A single horizon pays the two native charges for every label before the
sites, cutoffs, periods and microscopic test values are chosen. -/
theorem names (d : ℕ) : ∃ H : ℕ,∀ q t : (R.family.labels.level d).Index,
    fieldToll (nativeGrade (seat R d q))+fieldToll (nativeGrade (seat R d t))≤H := by
  classical
  let T := Finset.univ.sup fun q : (R.family.labels.level d).Index=>fieldToll (nativeGrade (seat R d q))
  have one (q : (R.family.labels.level d).Index) : fieldToll (nativeGrade (seat R d q)) ≤ T :=
    Finset.le_sup (f:=fun z : (R.family.labels.level d).Index=>fieldToll (nativeGrade (seat R d z))) (Finset.mem_univ q)
  exact ⟨T+T,fun q t=>Nat.add_le_add (one q) (one t)⟩

end YM.Integration.WilsonOrdinaryUltravioletPair
