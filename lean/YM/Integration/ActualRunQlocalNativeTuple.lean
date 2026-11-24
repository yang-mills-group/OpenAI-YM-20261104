import YM.Integration.ActualRunQlocalPageInput
import YM.Integration.QlocalPageScaling
import YM.Integration.QlocalSignedReadout
import YM.Integration.QlocalNativeReadout
import YM.Integration.ActualRG05NativeAtoms

/-! One original atom choice at each marker, with its literal spatial root,
complex coefficient and full vacuum. The orientation is a budget-preserving
test-coordinate involution. Distinct tuples are not merged into one root. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunQlocalNativeTuple
open Function Finset Lattice Wilson RG Source Labels Marker FVA1
open PhysicalNext.Repeat.Legato Extra.Histories MergeProof MergeProof.Accent
open RG05Readout RG05Readout.Native RG05Readout.Nuclear RG05Readout.Flatten
open RG05Readout.Address RG05Readout.Records RG05Readout.Records.Basket
open RG3.Script.Picnic
open LocalComparison ComparisonDensity.Address
open scoped Classical BigOperators

variable {G : Gauge}

/-- All entries are original finite atom choices and test orders. -/
structure Datum (R : Run G) (p L n : ℕ) (hn : n ≤ L) (V : Type) where
  degree : V → ℕ
  origin : V → Site (R.family.side n p)
  motion : V → Motion
  palette : ∀ i, Palette R.family (degree i)
  choice : ∀ i, Site (R.family.S.toDepth hn p).count × Mark R.family (degree i)
  order : V → ℕ
  weight : V → ℕ
  depth_le : ∀ i, depth (choice i).2.1 ≤ order i

variable {R : Run G} {p L n : ℕ} {hn : n ≤ L} {V : Type}
  [DecidableEq V] [Fintype V] [Nonempty V]
  (D : Datum R p L n hn V)

abbrev grade (i : V) : ℕ := kept (D.choice i).2.1
abbrev label (i : V) : R.family.label (grade D i) :=
  ActualRG05NativeAtoms.nativeLabel R.family (D.degree i) (D.motion i) (D.choice i).2
abbrev root (i : V) : Site (R.family.side L p) :=
  ActualRG05NativeAtoms.location R.family L p n hn D.degree D.origin D.motion
    ⟨i, D.choice i⟩

/-- The stub is the original section footprint at that atom's own root. -/
def positions : Positions V (R.family.side L p) where
  origin := root D
  stub i := (R.family.localSection (grade D i)).footprint (root D i)
  mem i := Finset.mem_image.mpr
    ⟨0, (R.makes.sections (grade D i)).anchored, by simp⟩

abbrev orbit (i : V) : Orbit := QlocalNativeTests.orbit (D.order i) (D.weight i)
abbrev constant (i : V) : ℂ :=
  ratioX (R.family.S.toDepth hn p) (D.degree i) * val (D.palette i) (D.choice i).2

def reader (i : V) : (orbit D i).Mood →ₗ[ℂ] ℂ :=
  QlocalSignedReadout.native (orbit D i) (D.motion i) (constant D i)
    (D.choice i).2.1 (D.depth_le i)
    (placeR (R.family.S.toDepth hn p) (D.choice i).1)
    (((R.family.S.toDepth hn p).count.val : ℝ)⁻¹)

omit [DecidableEq V] [Fintype V] [Nonempty V] in
/-- Its price retains the original affine scale, coordinate map and basis. -/
theorem reader_bound (i : V) (f : (orbit D i).Mood) {b : ℝ}
    (hf : (orbit D i).Bill f.val b) :
    ‖reader D i f‖ ≤ ‖constant D i‖ *
      ((((R.family.S.toDepth hn p).count.val : ℝ)⁻¹) ^ depth (D.choice i).2.1 *
        (NativeCalibrationMoodReadout.coordinateCost (depth (D.choice i).2.1) *
          ((orbit D i).height (ActualRunCalibrationTests.coordinates.symm
            (placeR (R.family.S.toDepth hn p) (D.choice i).1)) * b))) := by
  apply QlocalSignedReadout.native_bound
  · positivity
  · exact hf
  · exact Set.mem_univ _

omit [DecidableEq V] [Fintype V] [Nonempty V] in
/-- No conjugation rule for the arbitrary native coefficient basis is used. -/
theorem reader_native (i : V) (f : Body) {c : ℝ}
    (hf : Tall (E := E4) f (D.order i) 1 c) :
    reader D i (QlocalOrientedTests.orientedMood (orbit D i) (D.motion i).2
      (QlocalNativeTests.nativeTest (D.order i) (D.weight i) f hf)) =
    ActualRG05NativeAtoms.amplitude R.family L p (D.degree i) n hn
      (D.motion i) (D.palette i) f (D.choice i).1 (D.choice i).2 := by
  rw [reader, QlocalSignedReadout.native_recover,
    QlocalNativeReadout.readout_feeR]
  simp only [ActualRG05NativeAtoms.amplitude, constant, mul_assoc]

omit [DecidableEq V] [Fintype V] [Nonempty V] in
/-- The original finer cutoff and the native terminal presentation have the
same BudgetPoint, using the actual representation receipts on both sides. -/
theorem kernel_agreement (N : ℕ) (hL : L ≤ N) (i : V) :
    ActualRunPhysicalPages.kernel R N p L (grade D i) (label D i)
      ((positions D).origin i) =
    ActualRG05NativeAtoms.kernels R.family L p n hn D.degree D.origin D.motion
      ⟨i, D.choice i⟩ := by
  have ht : (R.family.path.rep N p L).p.threshold =
      (R.family.path.rep L p L).p.threshold :=
    congrArg BudgetPoint.threshold
      ((R.makes.wilson.represents N p L hL).vac.trans
        (R.makes.wilson.represents L p L le_rfl).vac.symm)
  change Push.Local.presented (R.family.localSection (grade D i)) (root D i)
      (R.family.path.rep N p L).p.threshold (label D i) =
    Push.Local.presented (R.family.localSection (grade D i)) (root D i)
      (R.family.path.rep L p L).p.threshold (label D i)
  rw [ht]

def input (hG : G.Simple) (N : ℕ) (hL : L ≤ N) :
    Taste (TestSpace (orbit D)) (positions D).origin
      (R.family.path.rep N p L) (Stock.census V) :=
  ActualRunQlocalPageInput.input R hG N p L hL (positions D)
    (grade D) (label D) (orbit D) (reader D)

theorem active_zero (hG : G.Simple) (N : ℕ) (hL : L ≤ N) :
    ((input D hG N hL).leaf (fun i => (0 : (orbit D i).Mood))).Active :=
  ActualRunQlocalPageInput.active_zero R hG N p L hL (positions D)
    (grade D) (label D) (orbit D) (reader D)

theorem multilinear (hG : G.Simple) (N : ℕ) (hL : L ≤ N) :
    LocalComparison.Multilinear (orbit D) (input D hG N hL) :=
  ActualRunQlocalPageInput.multilinear R hG N p L hL (positions D)
    (grade D) (label D) (orbit D) (reader D)

theorem retains (hG : G.Simple) (N : ℕ) (hL : L ≤ N) :
    FunctionalRetains (input D hG N hL) (positions D).stub :=
  ActualRunQlocalPageInput.retains R hG N p L hL (positions D)
    (grade D) (label D) (orbit D) (reader D)

/-- Full original-vacuum density for every finite-smooth independent test. -/
theorem density_birth (hG : G.Simple) (N : ℕ) (hL : L ≤ N)
    (href : ∀ i, R.family.ref (grade D i) ≤ L)
    (x : TestSpace (orbit D)) (U : Config G (R.family.side L p)) :
    ((input D hG N hL).leaf x).density U =
    birth (Stock.census V) (R.family.path.rep N p L)
      (fun i W => reader D i (x i) *
        ActualRunPhysicalPages.kernel R N p L (grade D i) (label D i)
          ((positions D).origin i) W) U := by
  rw [input, ActualRunQlocalPageInput.density_pages]
  exact QlocalPageScaling.actual_essence R hG N p L hL (positions D)
    (grade D) (label D) href (fun i => reader D i (x i)) U

/-- The same fixed Taste recovers every original smooth-test tuple after
its prescribed orientation. The scalar factors and actual roots are literal. -/
theorem density_native (hG : G.Simple) (N : ℕ) (hL : L ≤ N)
    (href : ∀ i, R.family.ref (grade D i) ≤ L)
    (f : V → Body) (c : V → ℝ)
    (hf : ∀ i, Tall (E := E4) (f i) (D.order i) 1 (c i))
    (U : Config G (R.family.side L p)) :
    ((input D hG N hL).leaf (fun i =>
      QlocalOrientedTests.orientedMood (orbit D i) (D.motion i).2
        (QlocalNativeTests.nativeTest (D.order i) (D.weight i) (f i) (hf i)))).density U =
    birth (Stock.census V) (R.family.path.rep N p L)
      (fun i W => ActualRG05NativeAtoms.amplitude R.family L p (D.degree i) n hn
        (D.motion i) (D.palette i) (f i) (D.choice i).1 (D.choice i).2 *
        ActualRG05NativeAtoms.kernels R.family L p n hn D.degree D.origin D.motion
          ⟨i, D.choice i⟩ W) U := by
  rw [density_birth D hG N hL href]
  simp_rw [reader_native D, kernel_agreement D N hL]

end YM.Integration.ActualRunQlocalNativeTuple
