import YM.Integration.ActualOriginalCalibratedColumns
import YM.Integration.ActualRunQlocalTupleReaders
import YM.Integration.ActualRunKernelPackets

/-! The full finite Glyph list of the same prescription Q, with the existing
original native test reader at each marker.  Threshold compensation is an
exact inverse in the original Frame; it is not a replacement field or a
coefficient-only identification.  The clock and each coefficient order are
explicit.  This file does not select a new analytic input or assert an
admitted or cutoff-uniform cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOriginalQReaders

open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open MS MS.Landau MS.Swirl MS.Swirl.Near MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal
open MS.Native MS.Book MS.Puff MS.Puff.Mom MS.Puff.Engine MS.Puff.SplitP MS.Puff.Actors
open MS.Book.Convolve MS.Book.Program MS.Native.Wilsonian
open MSBar Barr Bric Inlay Odom MS.Land MS.Menus MS.Rake
open RG05Readout RG05Readout.Native RG05Readout.Address
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V]
  (Q : MS.Land.Prescription B)
  (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ)

/-- The original marker and every original calibrated Glyph, without merging. -/
abbrev Slot := (i : V) × MS.Menus.Glyph B (u i).h

def fee (s : Slot u) : ℂ :=
  oil (Q.fees (u s.1).h (u s.1).item) s.2 (orders s.1) μ

def coordinates (s : Slot u) : R.family.label s.2.size :=
  ActualOriginalDictionary.coordinates R B s.2.size s.2.grade s.2.2.2

/-- Full fixed-Q scalar times the already-constructed native linear reader. -/
def readers (s : Slot u) :
    (ActualRunQlocalNativeTuple.orbit D s.1).Mood →ₗ[ℂ] ℂ :=
  fee Q u μ orders s • ActualRunQlocalNativeTuple.reader D s.1

def readerPrice (i : V) : ℝ :=
  ‖ActualRunQlocalNativeTuple.constant D i‖ *
    ((((R.family.S.toDepth hn p).count.val : ℝ)⁻¹) ^ depth (D.choice i).2.1 *
      (NativeCalibrationMoodReadout.coordinateCost (depth (D.choice i).2.1) *
        (ActualRunQlocalNativeTuple.orbit D i).height
          (ActualRunCalibrationTests.coordinates.symm
            (RG05Readout.Flatten.placeR (R.family.S.toDepth hn p) (D.choice i).1))))

omit [DecidableEq V] in
theorem native_reader_bound (i : V)
    (x : IndependentTests (ActualRunQlocalNativeTuple.orbit D)) :
    ‖ActualRunQlocalNativeTuple.reader D i
        (testInclusion (ActualRunQlocalNativeTuple.orbit D) x i)‖ ≤ readerPrice D i := by
  simpa only [readerPrice, mul_one] using
    ActualRunQlocalNativeTuple.reader_bound D i
      (testInclusion (ActualRunQlocalNativeTuple.orbit D) x i) (x i).property

/-- Scale the coefficient coordinates, leaving every original observable fixed. -/
def scaledCoordinates (N : ℕ) (s : Slot u) : R.family.label s.2.size :=
  (R.family.labels.level s.2.size).scaled
    (R.family.path.rep N p L).p.threshold (coordinates (R := R) u s)

def labels (N : ℕ) (s : Slot u)
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D)) : R.family.label s.2.size :=
  readers Q D u μ orders s (x s.1) •
    scaledCoordinates (R := R) (p := p) (L := L) u N s

def coefficientBudget (N : ℕ) (s : Slot u)
    (j : (R.family.labels.level s.2.size).Index) : ℝ :=
  (‖fee Q u μ orders s‖ * readerPrice D s.1) *
    ‖scaledCoordinates (R := R) (p := p) (L := L) u N s j‖

omit [DecidableEq V] in
/-- A derived finite coefficient bill; it contains every fee and frame weight. -/
theorem coordinate_bound (N : ℕ) (s : Slot u)
    (j : (R.family.labels.level s.2.size).Index)
    (x : IndependentTests (ActualRunQlocalNativeTuple.orbit D)) :
    ‖labels Q D u μ orders N s
        (testInclusion (ActualRunQlocalNativeTuple.orbit D) x) j‖ ≤
      coefficientBudget Q D u μ orders N s j := by
  change ‖fee Q u μ orders s *
      ActualRunQlocalNativeTuple.reader D s.1
        (testInclusion (ActualRunQlocalNativeTuple.orbit D) x s.1) *
      scaledCoordinates (R := R) (p := p) (L := L) u N s j‖ ≤ _
  rw [norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (native_reader_bound D s.1 x) (norm_nonneg _))
    (norm_nonneg _)

omit [DecidableEq V] in
/-- The full calibrated coefficient still reads only its original native slot. -/
theorem coordinate_reads (N : ℕ) (s : Slot u)
    (j : (R.family.labels.level s.2.size).Index)
    (S : Support (R.family.side L p))
    (hS : (ActualRunQlocalNativeTuple.positions D).stub s.1 ⊆ S) :
    Comparison.Density.Testing.Reads (ActualRunQlocalNativeTuple.readerRegion D)
      S {s.1} (fun x => labels Q D u μ orders N s x j) := by
  intro x y h
  exact congrArg (fun z : ℂ => fee Q u μ orders s * z *
    scaledCoordinates (R := R) (p := p) (L := L) u N s j)
      (h s.1 (Finset.mem_singleton_self s.1) hS)

/-- No equality between separate test slots or coefficient bases is used. -/
theorem coordinate_letter (N : ℕ) (s : Slot u)
    (j : (R.family.labels.level s.2.size).Index) :
    RG3.Held.Letter ℂ (fun i => (ActualRunQlocalNativeTuple.orbit D i).Mood)
      {s.1} (fun x => labels Q D u μ orders N s x j) := by
  have h : RG3.Held.Letter ℂ
      (fun i => (ActualRunQlocalNativeTuple.orbit D i).Mood) {s.1}
      (fun x => readers Q D u μ orders s (x s.1)) := by
    constructor
    · intro x y he
      exact congrArg (readers Q D u μ orders s)
        (he s.1 (Finset.mem_singleton_self s.1))
    · intro x i hi a b
      have he : i = s.1 := Finset.mem_singleton.mp hi
      subst i
      simp
    · intro x i hi a b
      have he : i = s.1 := Finset.mem_singleton.mp hi
      subst i
      simp
  have he : (fun x => labels Q D u μ orders N s x j) =
      (fun x => scaledCoordinates (R := R) (p := p) (L := L) u N s j *
        readers Q D u μ orders s (x s.1)) := by
    funext x
    exact mul_comm _ _
  exact Eq.mpr
    (congrArg (fun f : TestSpace (ActualRunQlocalNativeTuple.orbit D) → ℂ =>
      RG3.Held.Letter ℂ
        (fun i => (ActualRunQlocalNativeTuple.orbit D i).Mood) {s.1} f) he)
    (h.cmul _)

omit [DecidableEq V] in
/-- Exact full-function cancellation of the actual threshold normalization. -/
theorem kernel_coordinates (N : ℕ) (s : Slot u)
    (z : Site (R.family.side L p)) (U : Config G (R.family.side L p)) :
    ActualRunPhysicalPages.kernel R N p L s.2.size
      (scaledCoordinates (R := R) (p := p) (L := L) u N s) z U =
      (R.family.localSection s.2.size).places (coordinates (R := R) u s) z U := by
  change (R.family.localSection s.2.size).places
    ((R.family.labels.level s.2.size).scaled (R.family.path.rep N p L).p.threshold⁻¹
      ((R.family.labels.level s.2.size).scaled (R.family.path.rep N p L).p.threshold
        (coordinates (R := R) u s))) z U = _
  have he := (R.family.labels.level s.2.size).scaled_inv
    (inv_ne_zero (R.family.path.rep N p L).p.threshold_pos.ne')
    (coordinates (R := R) u s)
  simpa only [inv_inv] using congrArg
    (fun v => (R.family.localSection s.2.size).places v z U) he

omit [DecidableEq V] in
theorem kernel_label (N : ℕ) (s : Slot u)
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (z : Site (R.family.side L p)) (U : Config G (R.family.side L p)) :
    ActualRunPhysicalPages.kernel R N p L s.2.size
      (labels Q D u μ orders N s x) z U =
      readers Q D u μ orders s (x s.1) *
        (R.family.localSection s.2.size).places (coordinates (R := R) u s) z U := by
  change (Push.Local.presented (R.family.localSection s.2.size) z
    (R.family.path.rep N p L).p.threshold)
      (readers Q D u μ orders s (x s.1) •
        scaledCoordinates (R := R) (p := p) (L := L) u N s) U = _
  rw [map_smul, Pi.smul_apply, smul_eq_mul]
  exact congrArg (fun z => readers Q D u μ orders s (x s.1) * z)
    (kernel_coordinates u N s z U)

omit [DecidableEq V] in
/-- Every Glyph in the same Q column contributes to the original full observable.
The original marker reader and original physical root remain fixed. -/
theorem column_read (N : ℕ) (i : V)
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (U : Config G (R.family.side L p)) :
    (∑ g : MS.Menus.Glyph B (u i).h,
      ActualRunPhysicalPages.kernel R N p L g.size
        (labels Q D u μ orders N ⟨i, g⟩ x) (ActualRunQlocalNativeTuple.root D i) U) =
      ActualRunQlocalNativeTuple.reader D i (x i) *
        ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) μ
          (R.family.side L p) (ActualRunQlocalNativeTuple.root D i) U (orders i) := by
  rw [ActualOriginalCalibratedColumns.weighted_observable_original, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [kernel_label Q D u μ orders N ⟨i, g⟩ x]
  change (fee Q u μ orders ⟨i, g⟩ *
      ActualRunQlocalNativeTuple.reader D i (x i)) * _ =
    ActualRunQlocalNativeTuple.reader D i (x i) * (_ * _)
  dsimp only [fee, coordinates]
  ring

end YM.Integration.ActualOriginalQReaders
end
