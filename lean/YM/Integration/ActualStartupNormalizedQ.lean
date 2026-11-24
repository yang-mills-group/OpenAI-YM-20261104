import YM.Integration.ActualRunReducedNormalization
import YM.Integration.ActualRequestedStartupPhysical
import YM.Integration.ActualOriginalQInput
import YM.Extra.MULTISOURCE_TRAJECTORIES.Initial

/-! Exact normalized integrals for the original startup action and full Q
coefficient columns. The complete original gas, startup remainder and
calibration remain. All independent tests and all original modes are retained;
their integrability follows from the original continuous finite stencils. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualStartupNormalizedQ

open Function Finset MeasureTheory Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison
open IterationFour IterationFour.Vacuum FullQLocal.RenderedStep
open MergeProof MergeProof.Accent
open scoped Classical BigOperators

variable {G : Gauge} {V : Type} (R : Run G)
    (J : Request V) (A : NumericSchedule R.family J) (m period : ℕ)

def action (U : Config G (R.family.side (m + 1) period)) : ℝ :=
  let X := R.family.path.rep (m + 1) period (m + 1)
  X.path.inChannels X.clip X.p
      (R.family.path.β (m + 1) period (m + 1)) U +
    Render.renders
      (Render.prefactor
        (Pert.Asymptotics.regulatorRun R.family (m + 1) period (m + 1)))
      X.p U
      (ActualStartupInvoice.paidAlbum G (R.family.side (m + 1) period)
        (A.inputNorm m) (R.family.path.levels.params (m + 1))
        J.order (A.inputWidth m)) +
    (ActualStartupMaskedAction.remainder R (m + 1) period J.order).amount
      (A.inputNorm m) U +
    (ActualRequestedStartupPhysical.calibration R J A m period).amount U

def weight (U : Config G (R.family.side (m + 1) period)) : ℝ :=
  let X := R.family.path.rep (m + 1) period (m + 1)
  Real.exp (-action R J A m period U) * X.activities.gas X.p U

/-- Both real remainders and the entire original gas remain after the
single field-independent scalar is removed. -/
theorem density_eq (T : Campaign R)
    (U : Config G (R.family.side (m + 1) period)) :
    ActualRunReducedNormalization.density R (m + 1) period (m + 1) U =
      weight R J A m period U := by
  let X := R.family.path.rep (m + 1) period (m + 1)
  have he := ActualRequestedStartupPhysical.physical_exponent R J A T m period U
  have hh : -X.scalar + X.exponent U = -action R J A m period U := by
    dsimp only [X] at *
    rw [he]
    unfold action
    ring
  change Real.exp (-X.scalar) *
    (Real.exp (X.exponent U) * X.activities.gas X.p U) =
      Real.exp (-action R J A m period U) * X.activities.gas X.p U
  rw [← mul_assoc, ← Real.exp_add, hh]

/-- The complete startup weight has exactly the original partition mass. -/
theorem mass_eq (T : Campaign R) :
    (∫ U, weight R J A m period U ∂prior G (R.family.side (m + 1) period)) =
      Real.exp (-(R.family.path.rep (m + 1) period (m + 1)).scalar) *
        partition G (R.family.side (m + 1) period) (R.family.beta (m + 1) period) := by
  have h := ActualRunReducedNormalization.mass_eq R (m + 1) period (m + 1) le_rfl
  unfold ActualRunReducedNormalization.mass at h
  simpa only [density_eq R J A m period T] using h

theorem mass_pos (T : Campaign R) :
    0 < ∫ U, weight R J A m period U ∂prior G (R.family.side (m + 1) period) := by
  rw [mass_eq R J A m period T]
  exact mul_pos (Real.exp_pos _) (partition_pos _)

section Columns
variable {R} {B : MS.Local.Physical.Deck G}
    (Q : MS.Land.Prescription B)

/-- Every complete fee-weighted original column is continuous on the full
physical configuration space, not just near the identity. -/
theorem column_continuous (u : MS.Rake.Label B) (μ : ℝ)
    (n : Side) (z : Site n) (k : ℕ) :
    Continuous (fun U =>
      ActualOriginalCalibratedColumns.weightedObservable R B Q u μ n z U k) := by
  have he (U : Config G n) :
      ActualOriginalCalibratedColumns.weightedObservable R B Q u μ n z U k =
        ∑ g : MS.Menus.Glyph B u.h,
          MS.Menus.oil (Q.fees u.h u.item) g k μ *
            (((ActualOriginalDictionary.dictionary R B).cylinder
              g.size g.grade g.2.2).O n z U : ℂ) := by
    unfold ActualOriginalCalibratedColumns.weightedObservable
      WilsonComparison.Finite.Dictionary.calibrated
    rw [List.map_map, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList,
      ← Finset.sum]
    rfl
  simp_rw [he]
  exact continuous_finsetSum Finset.univ fun g _ =>
    continuous_const.mul
      (Complex.continuous_ofReal.comp
        (((ActualOriginalDictionary.dictionary R B).cylinder
          g.size g.grade g.2.2).continuous n z))

variable {m period} [DecidableEq V] [Fintype V] [Nonempty V]
    {n : ℕ} {hn : n ≤ m + 1}
    (D : ActualRunQlocalNativeTuple.Datum R period (m + 1) n hn V)
    (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ)

def modeObservable (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (s : (Stock.census V).Mode)
    (U : Config G (R.family.side (m + 1) period)) : ℂ :=
  ∏ i ∈ s.val, ActualRunQlocalNativeTuple.reader D i (x i) *
    ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) μ
      (R.family.side (m + 1) period) (ActualRunQlocalNativeTuple.root D i) U (orders i)

omit [Nonempty V] in
theorem mode_continuous (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (s : (Stock.census V).Mode) :
    Continuous (modeObservable Q D u μ orders x s) := by
  exact continuous_finsetProd s.val fun i _ =>
    continuous_const.mul (column_continuous Q (u i) μ _ _ (orders i))

omit [Nonempty V] in
/-- Integrability is supplied for every independent test tuple and mode. -/
theorem mode_integrable (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (s : (Stock.census V).Mode) :
    Integrable (modeObservable Q D u μ orders x s)
      (law G (R.family.side (m + 1) period) (R.family.beta (m + 1) period)) := by
  exact Wilson.continuous_integrable _ (mode_continuous Q D u μ orders x s)

/-- This is a coefficient of the complete original Taste density, including
all original forced gas rows. It is not a replacement marked numerator. -/
theorem input_density_mode (hG : G.Simple)
    (href : ∀ a : ActualOriginalQReaders.Slot u, R.family.ref a.2.size ≤ m + 1)
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (s : (Stock.census V).Mode)
    (U : Config G (R.family.side (m + 1) period)) :
    (((ActualOriginalQInput.input Q D u μ orders hG (m + 1) le_rfl).leaf x).density U).part s =
      ((R.family.path.rep (m + 1) period (m + 1)).eval U : ℂ) *
        modeObservable Q D u μ orders x s U := by
  rw [ActualOriginalQInput.density_full Q D u μ orders hG (m + 1) le_rfl href]
  change (((R.family.path.rep (m + 1) period (m + 1)).eval U : ℂ) •
    Poly.pass (Mach (Stock.census V) _)).part s = _
  rw [Poly.part_smul, Mach, Extra.Trajectories.pass_fire]
  rfl

/-- The actual full-input numerator is integrable against product Haar. -/
theorem input_integrable (hG : G.Simple)
    (href : ∀ a : ActualOriginalQReaders.Slot u, R.family.ref a.2.size ≤ m + 1)
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (s : (Stock.census V).Mode) :
    Integrable (fun U =>
      (((ActualOriginalQInput.input Q D u μ orders hG (m + 1) le_rfl).leaf x).density U).part s)
      (prior G (R.family.side (m + 1) period)) := by
  have hb : (R.family.path.rep (m + 1) period (m + 1)).eval =
      bare (R.family.beta (m + 1) period) :=
    (R.makes.wilson.starts (m + 1) period).2
  have hc : Continuous (fun U : Config G (R.family.side (m + 1) period) =>
      (bare (R.family.beta (m + 1) period) U : ℂ) *
        modeObservable Q D u μ orders x s U) :=
    (Complex.continuous_ofReal.comp (bare_cont _)).mul
      (mode_continuous Q D u μ orders x s)
  convert hc.integrable_of_hasCompactSupport
    (μ := prior G (R.family.side (m + 1) period))
    (HasCompactSupport.of_compactSpace _) using 1
  funext U
  rw [input_density_mode Q D u μ orders hG href, hb]

omit [Nonempty V] in
/-- The physical numerator is also a genuine integral, with the full
remainder, calibration and gas retained. -/
theorem weighted_mode_integrable (J : Request V) (A : NumericSchedule R.family J)
    (T : Campaign R) (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (s : (Stock.census V).Mode) :
    Integrable (fun U => (weight R J A m period U : ℂ) *
      modeObservable Q D u μ orders x s U)
      (prior G (R.family.side (m + 1) period)) := by
  have hb : (R.family.path.rep (m + 1) period (m + 1)).eval =
      bare (R.family.beta (m + 1) period) :=
    (R.makes.wilson.starts (m + 1) period).2
  have hc : Continuous (fun U : Config G (R.family.side (m + 1) period) =>
      (bare (R.family.beta (m + 1) period) U : ℂ) *
        modeObservable Q D u μ orders x s U) :=
    (Complex.continuous_ofReal.comp (bare_cont _)).mul
      (mode_continuous Q D u μ orders x s)
  have hi := (hc.integrable_of_hasCompactSupport
    (μ := prior G (R.family.side (m + 1) period))
    (HasCompactSupport.of_compactSpace _)).const_mul
      (Real.exp (-(R.family.path.rep (m + 1) period (m + 1)).scalar) : ℂ)
  convert hi using 1
  funext U
  rw [← density_eq R J A m period T]
  simp only [ActualRunReducedNormalization.density, Complex.ofReal_mul, hb, mul_assoc]

omit [Nonempty V] in
/-- Exact original Wilson expectation as the normalized startup integral.
No additional integrability, analytic-color or vacuum-identification premise
is required for these full original-Q observables. -/
theorem original_expectation (J : Request V) (A : NumericSchedule R.family J)
    (T : Campaign R) (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (s : (Stock.census V).Mode) :
    R.family.omega (m + 1) period (modeObservable Q D u μ orders x s) =
      ((∫ U, weight R J A m period U
        ∂prior G (R.family.side (m + 1) period) : ℝ) : ℂ)⁻¹ *
        ∫ U, (weight R J A m period U : ℂ) * modeObservable Q D u μ orders x s U
          ∂prior G (R.family.side (m + 1) period) := by
  rw [← ActualRunReducedNormalization.original_average R (m + 1) period
    (modeObservable Q D u μ orders x s) (mode_integrable Q D u μ orders x s)]
  unfold ActualRunReducedNormalization.average ActualRunReducedNormalization.mass
  simp_rw [density_eq R J A m period T]

/-- The supplied full Q-input coefficient, normalized by the original
partition, is the same physical normalized integral. All modes, including
the vacuum mode, use this single denominator. -/
theorem input_normalized (hG : G.Simple)
    (href : ∀ a : ActualOriginalQReaders.Slot u, R.family.ref a.2.size ≤ m + 1)
    (J : Request V) (A : NumericSchedule R.family J) (T : Campaign R)
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (s : (Stock.census V).Mode) :
    (partition G (R.family.side (m + 1) period)
      (R.family.beta (m + 1) period) : ℂ)⁻¹ *
      ∫ U, (((ActualOriginalQInput.input Q D u μ orders hG (m + 1) le_rfl).leaf x).density U).part s
        ∂prior G (R.family.side (m + 1) period) =
    ((∫ U, weight R J A m period U
      ∂prior G (R.family.side (m + 1) period) : ℝ) : ℂ)⁻¹ *
      ∫ U, (weight R J A m period U : ℂ) * modeObservable Q D u μ orders x s U
        ∂prior G (R.family.side (m + 1) period) := by
  simp_rw [input_density_mode Q D u μ orders hG href]
  exact (ActualRunCoarseReadout.original_readout R (m + 1) period
    (modeObservable Q D u μ orders x s) (mode_integrable Q D u μ orders x s)).trans
      (original_expectation Q D u μ orders J A T x s)

end Columns
end YM.Integration.ActualStartupNormalizedQ
end
