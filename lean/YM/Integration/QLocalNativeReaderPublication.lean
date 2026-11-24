import YM.Integration.ActualOriginalQReaders
import YM.Integration.QLocalCoefficientPublication

/-! The literal family of independent physical tests acts on every native
marker mode by the product of its original linear readers. This action
commutes with the complete vacuum birth, its true history push, and the
regular and forced switch readouts. Each coefficient has an explicit
pre-test charge using the original reader prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalNativeReaderPublication

open Function Finset Filter MeasureTheory Lattice Wilson RG Source Marker FVA1
open PhysicalNext.Repeat.Legato Extra.Histories Extra.Trajectories Merge MergeProof MergeProof.Accent
open RG3.Script.Picnic LocalComparison ComparisonDensity.Address
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {p L n : ℕ} {hn : n ≤ L} {V : Type}
  [DecidableEq V] [Fintype V] (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)

local notation "Tests" => IndependentTests (ActualRunQlocalNativeTuple.orbit D)
local notation "CensusV" => Stock.census V

/-- Each test is observed by its actual original affine coordinate reader. -/
def coefficients (x : Tests) (i : V) : ℂ :=
  ActualRunQlocalNativeTuple.reader D i (testInclusion (ActualRunQlocalNativeTuple.orbit D) x i)

omit [DecidableEq V] [Fintype V] in
theorem coefficient_bound (x : Tests) (i : V) :
    ‖coefficients D x i‖ ≤ ActualOriginalQReaders.readerPrice D i :=
  ActualOriginalQReaders.native_reader_bound D i x

def modePrice (q : (CensusV).Mode) : ℝ := ∏ i ∈ q.val, ActualOriginalQReaders.readerPrice D i

theorem weight_bound (x : Tests) (q : (CensusV).Mode) :
    ‖QlocalPageScaling.weight (coefficients D x) q‖ ≤ modePrice D q := by
  rw [QlocalPageScaling.weight, norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => coefficient_bound D x i)

/-- Transfer every mode, with the same positive product invoice, including
the empty product equal to one on the actual vacuum. -/
theorem mode_bound (x : Tests) (q : (CensusV).Mode) (Z : Poly CensusV) :
    ‖(NativeWeightedColors.fuse id (coefficients D x) Z).part q‖ ≤ modePrice D q * ‖Z.part q‖ := by
  rw [QlocalPageScaling.fuse_part, norm_mul]
  exact mul_le_mul_of_nonneg_right (weight_bound D x q) (norm_nonneg _)

theorem switch_natural {I : Type} [Fintype I] (γ : V → ℂ) (z : I → Poly CensusV) (k : Switch.Ways I) :
    NativeWeightedColors.fuse id γ (Switch.sound z k) =
      Switch.sound (fun i => NativeWeightedColors.fuse id γ (z i)) k := by
  unfold Switch.sound
  rw [Switch.mapScores_apply, Switch.mapScores_apply, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_smul, NativeWeightedColors.fuse_prod]

theorem switch_bound {I : Type} [Fintype I] (z : I → Poly CensusV) (k : Switch.Ways I)
    (x : Tests) (q : (CensusV).Mode) :
    ‖(Switch.sound (fun i => NativeWeightedColors.fuse id (coefficients D x) (z i)) k).part q‖ ≤
      modePrice D q * ‖(Switch.sound z k).part q‖ := by
  rw [← switch_natural (coefficients D x) z k]
  exact mode_bound D x q _

/-- A paid family of native ways has a common coefficient envelope over all
independent tests once the actual marker charges on its generators are paid. -/
theorem common_switch {I Y : Type} [Fintype I] (z : I → Poly CensusV) {F : Y → Switch.Ways I}
    {b : ℝ} (hF : Switch.Paid F b) {w : V → ℝ} (hw : ∀ i, 0 < w i)
    (hz : ∀ i, Poly.price w (NativeWeightedColors.fuse id
      (fun j => (ActualOriginalQReaders.readerPrice D j : ℂ)) (z i)) ≤ 1) :
    Accent.Loci w (fun y : Tests × Y => Switch.sound
      (fun i => NativeWeightedColors.fuse id (coefficients D y.1) (z i)) (F y.2)) b := by
  let γ (i : V) : ℂ := (ActualOriginalQReaders.readerPrice D i : ℂ)
  obtain ⟨a, ha, hb, hc⟩ := Accent.crystal hF hw hz
  refine ⟨a, ha, ?_, hc⟩
  intro y q
  apply (switch_bound D z (F y.2) y.1 q).trans
  have he : ‖QlocalPageScaling.weight γ q‖ = modePrice D q := by
    rw [QlocalPageScaling.weight, norm_prod]
    apply Finset.prod_congr rfl
    intro i _
    exact (Complex.norm_real _).trans (Real.norm_of_nonneg ((norm_nonneg _).trans (coefficient_bound D y.1 i)))
  have hb' := hb y.2 q
  change ‖(Switch.sound (fun i => NativeWeightedColors.fuse id γ (z i)) (F y.2)).part q‖ ≤ _ at hb'
  rwa [← switch_natural γ z, QlocalPageScaling.fuse_part, norm_mul, he] at hb'

abbrev kernel (N : ℕ) (i : V) := ActualRunPhysicalPages.kernel R N p L
  (ActualRunQlocalNativeTuple.grade D i) (ActualRunQlocalNativeTuple.label D i)
  ((ActualRunQlocalNativeTuple.positions D).origin i)

def source (N : ℕ) := Accent.birth CensusV (R.family.path.rep N p L) (kernel D N)

theorem source_integrable (N : ℕ) (hL : L ≤ N) :
    Integrable (source D N) (prior G (R.family.side L p)) := by
  let F (U : Config G (R.family.side L p)) := Poly.pass (Mach CensusV (fun i => kernel D N i U))
  have hk (i : V) : Continuous (kernel D N i) := (R.family.localSection _).continuous_places _ _
  have hF : Continuous F := by
    apply Poly.pass_cont.comp
    apply continuous_finsetSum
    intro i _
    change Continuous fun U => (Poly.send ((CensusV).fire i) (kernel D N i U)).part
    apply continuous_pi
    intro q
    simp_rw [Poly.part_send]
    split_ifs
    · exact hk i
    · exact continuous_const
  have hI := hF.integrable_of_hasCompactSupport (μ := prior G (R.family.side L p))
    (HasCompactSupport.of_compactSpace _)
  have hv := (R.family.path.rep N p L).envelope (R.makes.wilson.represents N p L hL).good
  obtain ⟨b, hb⟩ := hv.cost
  exact hI.bdd_smul (φ := fun U => ((R.family.path.rep N p L).eval U : ℂ)) b
    (Complex.continuous_ofReal.measurable.comp hv.meas).aestronglyMeasurable
    (Eventually.of_forall (fun U => by simpa only [Complex.norm_real] using hb U))

variable [Nonempty V]

theorem density (hG : G.Simple) (N : ℕ) (hL : L ≤ N)
    (href : ∀ i, R.family.ref (ActualRunQlocalNativeTuple.grade D i) ≤ L)
    (x : Tests) (U : Config G (R.family.side L p)) :
    ((ActualRunQlocalNativeTuple.input D hG N hL).leaf
      (testInclusion (ActualRunQlocalNativeTuple.orbit D) x)).density U =
      NativeWeightedColors.fuse id (coefficients D x) (source D N U) := by
  rw [ActualRunQlocalNativeTuple.density_birth D hG N hL href]
  have he := congrFun (NativeWeightedColors.fuse_birth (id : V → V) (coefficients D x)
    (R.family.path.rep N p L) (kernel D N)) U
  have hagg : JointSignedInitialization.Rooted.aggregate id (coefficients D x) (kernel D N) =
      fun i W => coefficients D x i * kernel D N i W := by
    funext i W
    unfold JointSignedInitialization.Rooted.aggregate
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  rw [hagg] at he
  exact he.symm

/-- The original independent unit tests pass through any number of the actual
history steps as one coefficient map. The native source pays integrability
on the given Run at its supplied period and finer cutoff. -/
theorem history (hG : G.Simple) (N : ℕ) (hL : L ≤ N)
    (href : ∀ i, R.family.ref (ActualRunQlocalNativeTuple.grade D i) ≤ L)
    (x : Tests) {m : ℕ} (hm : m ≤ L) :
    gust R.family.path N p L ((ActualRunQlocalNativeTuple.input D hG N hL).leaf
      (testInclusion (ActualRunQlocalNativeTuple.orbit D) x)).density m hm =
    fun U => NativeWeightedColors.fuse id (coefficients D x) (gust R.family.path N p L (source D N) m hm U) := by
  rw [funext (density D hG N hL href x)]
  exact NativeWeightedColors.fuse_gust id (coefficients D x) R.family.path N p L
    (source D N) (source_integrable D N hL) hm

end YM.Integration.QLocalNativeReaderPublication
end
