import YM.Integration.ActualLeadingIR

/-! The full original Wilson source film, in the native inversion-tree
coordinates and with its original slot divisions, supplies the leading
IR comparison. Normalization uses Bare's full action, Haar series and
vacuum denominator; products are formed before that normalization. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualLeadingSeries

open Function Filter Lattice Wilson Source PowerSeries
open RG06 RG06.WilsonCompiler XSpace XSpace.Chart2 XSpace.Outline XSpace.JetGauge
open Next.Rank.Normal ActualLeadingIR
open scoped BigOperators Classical Topology

/- The generic shift proof is the small algebraic interface used by
RG06.Floor, written locally to avoid importing its unvalidated branch. -/
def lowerFilm {A : Type*} [Semiring A] (n : ℕ) (F : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun k => PowerSeries.coeff (k + n) F

def Starts {A : Type*} [Semiring A] (n : ℕ) (F : PowerSeries A) : Prop :=
  ∀ k, k < n → PowerSeries.coeff k F = 0

theorem lowerFilm_coeff {A : Type*} [Semiring A] (n k : ℕ) (F : PowerSeries A) :
    coeff k (lowerFilm n F) = coeff (k + n) F := PowerSeries.coeff_mk ..

theorem restoreFilm {A : Type*} [CommRing A] {n : ℕ} {F : PowerSeries A}
    (h : Starts n F) : lowerFilm n F * PowerSeries.X ^ n = F := by
  ext k : 1
  by_cases hk : k < n
  · rw [h k hk, PowerSeries.coeff_mul_X_pow']
    simp [not_le.mpr hk]
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hk)
  rw [hr, Nat.add_comm, PowerSeries.coeff_mul_X_pow, lowerFilm_coeff]

variable {G : Gauge} (C : Family G) (N p d : ℕ)

/-- Exact calibrated physical film transported by the native tree's
linear cotree chart. No source polynomial is replaced. -/
def source (T : (actualPeriod C N p).Tree) (x : Site (C.side N p))
    (i : (C.labels.level d).Index) : Bare.Series T G :=
  PowerSeries.map (tea T).toRingHom
    (physicalFilm C N p d x (Dict06.Actual.calibrate C N p d ((C.labels.level d).basis i)))

theorem source_coeff (T : (actualPeriod C N p).Tree) (x : Site (C.side N p))
    (i : (C.labels.level d).Index) (k : ℕ) :
    coeff k (source C N p d T x i) = tea T (coeff k
      (physicalFilm C N p d x (Dict06.Actual.calibrate C N p d ((C.labels.level d).basis i)))) := by
  rfl

theorem source_below (hV : Bid.pop (C.localSection d))
    (T : (actualPeriod C N p).Tree) (x : Site (C.side N p))
    (i : (C.labels.level d).Index) :
    Starts ((C.labels.level d).grades i).2 (source C N p d T x i) := by
  intro k hk
  have hf : coeff k (physicalFilm C N p d x
      (Dict06.Actual.calibrate C N p d ((C.labels.level d).basis i))) = 0 := by
    rw [physicalFilm_periodize, PowerSeries.coeff_map, physicalCoverFilm,
      Dict06.Actual.meet, (C.labels.level d).coords_basis, PowerSeries.coeff_C_mul,
      markTop_coeff_casing, Tokens.doesNotStart (C.localSection d) hV i k hk,
      mul_zero, map_zero]
  rw [source_coeff]
  exact (congrArg (tea T) hf).trans (map_zero _)

/-- The original valuation justifies the slot division: multiplying back
recovers the complete source, not merely its tail after a projection. -/
theorem source_restore (hV : Bid.pop (C.localSection d))
    (T : (actualPeriod C N p).Tree) (x : Site (C.side N p))
    (i : (C.labels.level d).Index) :
    lowerFilm ((C.labels.level d).grades i).2 (source C N p d T x i) *
      PowerSeries.X ^ ((C.labels.level d).grades i).2 = source C N p d T x i :=
  restoreFilm (source_below C N p d hV T x i)

theorem source_leading (T : (actualPeriod C N p).Tree) (x : Site (C.side N p))
    (i : (C.labels.level d).Index) :
    coeff ((C.labels.level d).grades i).2 (source C N p d T x i) =
      tea T (((dawn G (actualPeriod C N p)).points x).pull
        (Dict06.Actual.factor C N d • Tokens.stencil (C.localSection d) i 0)) := by
  rw [source_coeff]
  have hh := physicalCoverFilm_basis_coeff C d N p i 0
  simp only [Tokens.charge, Nat.zero_add] at hh
  have hf : coeff ((C.labels.level d).grades i).2 (physicalFilm C N p d x
      (Dict06.Actual.calibrate C N p d ((C.labels.level d).basis i))) =
      MvPolynomial.rename (coverAddress x)
        (MvPolynomial.C (Dict06.Actual.factor C N d) * Tokens.stencil (C.localSection d) i 0) := by
    rw [physicalFilm_periodize, PowerSeries.coeff_map, hh]
    rfl
  apply (congrArg (tea T) hf).trans
  rw [MvPolynomial.smul_eq_C_mul]
  rfl

variable {I : Type*} [Fintype I] (degree : I → ℕ)

/-- Each column keeps its own original slot degree. Independent complex
mixtures are formed inside the complete normalized source product. -/
def series (T : (actualPeriod C N p).Tree) (x : I → Cover)
    (v : (i : I) → C.label (degree i)) : PowerSeries ℂ :=
  Bare.normalized T G (∏ i, ∑ j,
    v i j • lowerFilm ((C.labels.level (degree i)).grades j).2
      (source C N p (degree i) T (wrap (C.side N p) (x i)) j))

/-- Restoring all original slot powers commutes with the full native
normalization, including its one common interacting vacuum denominator. -/
theorem series_basis_restore (hV : ∀ i, Bid.pop (C.localSection (degree i)))
    (T : (actualPeriod C N p).Tree) (x : I → Cover) (b : Choices C degree) :
    PowerSeries.X ^ (∑ i, ((C.labels.level (degree i)).grades (b i)).2) *
      series C N p degree T x (basisInput C degree b) =
      Bare.normalized T G (∏ i, source C N p (degree i) T (wrap (C.side N p) (x i)) (b i)) := by
  have he : (∏ i, source C N p (degree i) T (wrap (C.side N p) (x i)) (b i)) =
      Bare.scalar T (PowerSeries.X ^ (∑ i, ((C.labels.level (degree i)).grades (b i)).2)) *
        (∏ i, lowerFilm ((C.labels.level (degree i)).grades (b i)).2
          (source C N p (degree i) T (wrap (C.side N p) (x i)) (b i))) := by
    rw [Bare.scalar, map_pow, PowerSeries.map_X, ← Finset.prod_pow_eq_pow_sum,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [mul_comm]
    exact (source_restore C N p (degree i) (hV i) T _ (b i)).symm
  rw [he, Bare.normalized_scalar]
  simp [series, basisInput, Pi.single_apply]

/-- The leading coefficient belongs to the full normalized series of the
actual calibrated source film, rather than a constant-polynomial surrogate. -/
theorem series_leading (T : (actualPeriod C N p).Tree) (x : I → Cover)
    (v : (i : I) → C.label (degree i)) :
    coeff 0 (series C N p degree T x v) =
      finite C degree (engineeredInput C degree N v) (actualPeriod C N p) T x := by
  rw [series, coeff_zero_eq_constantCoeff_apply, Bare.leading]
  unfold finite E
  rw [← transfers, marked_motor]
  congr 1
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [map_sum, PowerSeries.constantCoeff_smul]
  have hl (j : (C.labels.level (degree i)).Index) :
      constantCoeff (lowerFilm ((C.labels.level (degree i)).grades j).2
        (source C N p (degree i) T (wrap (C.side N p) (x i)) j)) =
      tea T (((dawn G (actualPeriod C N p)).points (wrap (C.side N p) (x i))).pull
        (Dict06.Actual.factor C N (degree i) • Tokens.stencil (C.localSection (degree i)) j 0)) := by
    rw [← coeff_zero_eq_constantCoeff_apply, lowerFilm_coeff, Nat.zero_add]
    exact source_leading C N p (degree i) T _ j
  simp_rw [hl]
  simp only [engineeredInput, leading, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j _
  change v i j • (Dict06.Actual.factor C N (degree i) • _) =
    (Dict06.Actual.factor C N (degree i) * v i j) • _
  rw [smul_smul, mul_comm]
  rfl

/-- One bound controls the actual normalized leading series for all
independent source coefficients and all original regulator periods. -/
theorem comparison (hV : ∀ i, Bid.pop (C.localSection (degree i))) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (N p : ℕ) (v : (i : I) → C.label (degree i))
      (T : (actualPeriod C N p).Tree) (o : Cover),
      Comets.Tall (actualPeriod C N p) o → ∀ (r : ℕ) (x : I → Cover),
      (∀ i, Sail.reach (x i - o) ≤ r) →
      engineeringScale C degree N *
        ‖coeff 0 (series C N p degree T x v) -
          cover C degree (engineeredInput C degree N v) x‖ ≤
        A * Comets.budget (actualPeriod C N p) r * inputMass C degree v := by
  obtain ⟨A, hA, H⟩ := comparison_engineered C degree hV
  refine ⟨A, hA, ?_⟩
  intro N p v T o ho r x hx
  rw [series_leading]
  exact H N v _ T o ho r x hx

/-- At fixed ultraviolet cutoff, the full actual normalized source series
has the same leading period limit. Independently chosen coefficients may
vary with the period inside one bounded finite-dimensional input mass. -/
theorem error_tendsto (hV : ∀ i, Bid.pop (C.localSection (degree i)))
    (N r : ℕ) (v : (p : ℕ) → (i : I) → C.label (degree i)) (M : ℝ)
    (hmass : ∀ᶠ p in atTop, inputMass C degree (v p) ≤ M)
    (T : (p : ℕ) → (actualPeriod C N p).Tree)
    (o : ℕ → Cover) (x : ℕ → I → Cover)
    (hbulk : ∀ᶠ p in atTop, Comets.Tall (actualPeriod C N p) (o p) ∧
      ∀ i, Sail.reach (x p i - o p) ≤ r) :
    Tendsto (fun p => coeff 0 (series C N p degree (T p) (x p) (v p)) -
      cover C degree (engineeredInput C degree N (v p)) (x p)) atTop (𝓝 0) := by
  have hm : ∀ᶠ p in atTop,
      inputMass C degree (engineeredInput C degree N (v p)) ≤
        M / engineeringScale C degree N := by
    filter_upwards [hmass] with p hp
    apply (le_div_iff₀ (engineeringScale_pos C degree N)).mpr
    rw [mul_comm, engineeredInput_mass]
    exact hp
  simpa only [series_leading] using
    actual_uniform_error_tendsto C degree hV N r
      (fun p => engineeredInput C degree N (v p))
      (M / engineeringScale C degree N) hm T o x hbulk

end YM.Integration.ActualLeadingSeries
