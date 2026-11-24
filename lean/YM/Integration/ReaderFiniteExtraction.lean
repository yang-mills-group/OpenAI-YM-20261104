import YM.OPE.Orbits.System
import YM.OPE.Detector
import YM.Integration.FixedHorizonReadout

/-!
Finite-output-horizon extraction for the already chosen orbit Reader.

The packet contains the original real, rotation-averaged `fresh` fields. A
finite detector recovers that field; it does not replace the averaged
prescription by unrotated raw-product evaluations. The two residuals below
remain distinct: ordinary OPE truncation, and the complete-product matching
comparison. Their analytic suppliers are not assumed to be interchangeable.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ReaderFiniteExtraction
open YM.OPE YM.OPE.Orbits
open scoped BigOperators Classical

variable {G : Gauge} {L : Register G} {S : Table L}
    {Q : DiffPlan S} {X : S.Rotation} {ρ : S.RealSpin}
    (R : Reader Q X ρ)

/-- Original homogeneous Reader coordinate of a finite-horizon physical field. -/
def coordinate (m D : ℕ) (j : R.channels m) : S.Field D →ₗ[ℂ] ℂ :=
  (R.basis m).coord j ∘ₗ
    (R.cutTest m D).codRestrict (R.stratum m)
      (fun z => R.knife_mem m (R.liftOne m D z))

/-- Increasing the ambient output horizon preserves the fixed coordinate. -/
lemma coordinate_rise (m D E : ℕ) (j : R.channels m) (h : D ≤ E)
    (z : S.Field D) :
    coordinate R m E j (Q.rise h z) = coordinate R m D j z := by
  apply congrArg (fun v : R.stratum m => (R.basis m).repr v j)
  apply Subtype.ext
  exact R.cut_rise m D E h z

variable {I : Type} [Fintype I] {d : I → ℕ}

/-- Exact extraction of the preserved Reader coefficient from every sufficient
finite output horizon. No spectator or perturbative order chooses the basis. -/
lemma coordinate_packet (m D : ℕ) (j : R.channels m) (h : m ≤ D)
    (x : I → E4) (v : Labels S d) (o : E4) :
    coordinate R m D j (R.packet D x v o) = R.coef m j x v o := by
  apply congrArg (fun z : R.stratum m => (R.basis m).repr z j)
  apply Subtype.ext
  exact R.filtered_packet m D h x v o

lemma coordinate_packet_coherent (m D E : ℕ) (j : R.channels m)
    (hD : m ≤ D) (hE : m ≤ E)
    (x : I → E4) (v : Labels S d) (o : E4) :
    coordinate R m D j (R.packet D x v o) =
      coordinate R m E j (R.packet E x v o) := by
  rw [coordinate_packet R m D j hD, coordinate_packet R m E j hE]

variable {D : ℕ} (U : Detector S D)

/-- A fixed finite physical detector followed by the original Reader coordinate.
Its norm depends on the chosen physical hierarchy, horizon and channel only. -/
def readout (m : ℕ) (j : R.channels m) : (Fin U.size → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap ((coordinate R m D j).comp U.report)

lemma readout_field (m : ℕ) (j : R.channels m) (z : S.Field D) :
    readout R U m j (fun i => witnessAt S D (U.listen i) z) =
      coordinate R m D j z := by
  change coordinate R m D j (U.report _) = _
  rw [U.recovered]

lemma readout_packet (m : ℕ) (j : R.channels m) (h : m ≤ D)
    (x : I → E4) (v : Labels S d) (o : E4) :
    readout R U m j (fun i => witnessAt S D (U.listen i) (R.packet D x v o)) =
      R.coef m j x v o := by
  rw [readout_field, coordinate_packet R m D j h]

/-- Equality of the finitely many actual physical tests suffices to identify
the retained coefficient in the original Reader prescription. -/
lemma coefficient_unique (m : ℕ) (j : R.channels m) (h : m ≤ D)
    (x : I → E4) (v : Labels S d) (o : E4) (z : S.Field D)
    (ht : ∀ i, witnessAt S D (U.listen i) (R.packet D x v o) =
      witnessAt S D (U.listen i) z) :
    R.coef m j x v o = coordinate R m D j z := by
  rw [← readout_packet R U m j h x v o, ← readout_field R U m j z]
  exact congrArg (readout R U m j) (funext ht)

/-- Pointwise finite-test errors pay the actual fixed extraction operator norm. -/
lemma coefficient_error_bound (m : ℕ) (j : R.channels m) (h : m ≤ D)
    (x : I → E4) (v : Labels S d) (o : E4) (z : S.Field D)
    (ε : ℝ) (hε : 0 ≤ ε)
    (ht : ∀ i, ‖witnessAt S D (U.listen i) (R.packet D x v o) -
      witnessAt S D (U.listen i) z‖ ≤ ε) :
    ‖R.coef m j x v o - coordinate R m D j z‖ ≤ ‖readout R U m j‖ * ε := by
  let a : Fin U.size → ℂ := fun i => witnessAt S D (U.listen i) (R.packet D x v o)
  let b : Fin U.size → ℂ := fun i => witnessAt S D (U.listen i) z
  have he : readout R U m j (a - b) =
      R.coef m j x v o - coordinate R m D j z := by
    rw [map_sub]
    exact congrArg₂ Sub.sub (readout_packet R U m j h x v o) (readout_field R U m j z)
  rw [← he]
  exact ((readout R U m j).le_opNorm (a - b)).trans
    (mul_le_mul_of_nonneg_left ((pi_norm_le_iff_of_nonneg hε).mpr ht)
      (readout R U m j).opNorm_nonneg)

/-- Separate OPE and complete-product comparison residuals are transported
through the same finite detector and the same original Reader coordinates. -/
lemma coefficient_two_residuals (m : ℕ) (j : R.channels m) (h : m ≤ D)
    (x : I → E4) (v : Labels S d) (o : E4) (z : S.Field D)
    (actual : Fin U.size → ℂ) (opeError matchingError : ℝ)
    (hO : 0 ≤ opeError) (hM : 0 ≤ matchingError)
    (ordinaryOPE : ∀ i, ‖actual i -
      witnessAt S D (U.listen i) (R.packet D x v o)‖ ≤ opeError)
    (completeProductMatch : ∀ i, ‖actual i -
      witnessAt S D (U.listen i) z‖ ≤ matchingError) :
    ‖R.coef m j x v o - coordinate R m D j z‖ ≤
      ‖readout R U m j‖ * (opeError + matchingError) := by
  apply coefficient_error_bound R U m j h x v o z _ (add_nonneg hO hM)
  intro i
  calc
    ‖witnessAt S D (U.listen i) (R.packet D x v o) - witnessAt S D (U.listen i) z‖ =
      ‖(actual i - witnessAt S D (U.listen i) z) -
        (actual i - witnessAt S D (U.listen i) (R.packet D x v o))‖ := by
          congr 1; ring
    _ ≤ ‖actual i - witnessAt S D (U.listen i) z‖ +
      ‖actual i - witnessAt S D (U.listen i) (R.packet D x v o)‖ := norm_sub_le _ _
    _ ≤ matchingError + opeError := add_le_add (completeProductMatch i) (ordinaryOPE i)
    _ = opeError + matchingError := add_comm _ _

/-- One finite constant covers every retained homogeneous channel. -/
def horizonPrice : ℝ :=
  ∑ m ∈ Finset.range (D + 1), ∑ j : R.channels m, ‖readout R U m j‖

lemma horizonPrice_nonneg : 0 ≤ horizonPrice R U := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma readout_le_horizonPrice (m : ℕ) (j : R.channels m) (h : m ≤ D) :
    ‖readout R U m j‖ ≤ horizonPrice R U := by
  calc
    ‖readout R U m j‖ ≤ ∑ j' : R.channels m, ‖readout R U m j'‖ :=
      Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ horizonPrice R U :=
      Finset.single_le_sum
        (f := fun k : ℕ => ∑ j : R.channels k, ‖readout R U k j‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le h))

/-- Uniform over every output channel, all positions, input fields and supplied
finite test data. No phase or perturbative-order parameter changes the constant. -/
lemma finite_horizon_two_residuals (m : ℕ) (j : R.channels m) (h : m ≤ D)
    (x : I → E4) (v : Labels S d) (o : E4) (z : S.Field D)
    (actual : Fin U.size → ℂ) (opeError matchingError : ℝ)
    (hO : 0 ≤ opeError) (hM : 0 ≤ matchingError)
    (ordinaryOPE : ∀ i, ‖actual i -
      witnessAt S D (U.listen i) (R.packet D x v o)‖ ≤ opeError)
    (completeProductMatch : ∀ i, ‖actual i -
      witnessAt S D (U.listen i) z‖ ≤ matchingError) :
    ‖R.coef m j x v o - coordinate R m D j z‖ ≤
      horizonPrice R U * (opeError + matchingError) :=
  (coefficient_two_residuals R U m j h x v o z actual opeError matchingError
    hO hM ordinaryOPE completeProductMatch).trans
      (mul_le_mul_of_nonneg_right (readout_le_horizonPrice R U m j h) (add_nonneg hO hM))

/-- The auxiliary finite detector is actually supplied by this Reader's
unchanged physical hierarchy. There is no matrix-invertibility premise. -/
def actualDetector (D : ℕ) : Detector S D :=
  FixedHorizonReadout.actualDetector R.continuum D

lemma actual_finite_horizon_bound (D : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (m : ℕ) (j : R.channels m), m ≤ D →
      ∀ (x : I → E4) (v : Labels S d) (o : E4) (z : S.Field D)
        (actual : Fin (actualDetector R D).size → ℂ)
        (opeError matchingError : ℝ), 0 ≤ opeError → 0 ≤ matchingError →
      (∀ i, ‖actual i - witnessAt S D ((actualDetector R D).listen i)
        (R.packet D x v o)‖ ≤ opeError) →
      (∀ i, ‖actual i - witnessAt S D ((actualDetector R D).listen i) z‖ ≤ matchingError) →
      ‖R.coef m j x v o - coordinate R m D j z‖ ≤ K * (opeError + matchingError) := by
  refine ⟨1 + horizonPrice R (actualDetector R D),
    add_pos_of_pos_of_nonneg zero_lt_one (horizonPrice_nonneg R _), ?_⟩
  intro m j hm x v o z actual opeError matchingError hO hM ordinaryOPE completeProductMatch
  exact (finite_horizon_two_residuals R (actualDetector R D) m j hm x v o z
    actual opeError matchingError hO hM ordinaryOPE completeProductMatch).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (add_nonneg hO hM))

open Filter Asymptotics

/-- A finite collection of little-o residuals transfers to the original
coefficient without losing the perturbative order. The index may contain
positions, fields, phase and independent tests; the readout remains fixed. -/
lemma coefficient_two_residuals_isLittleO {α E : Type*} {l : Filter α}
    [SeminormedAddCommGroup E] (m : ℕ) (j : R.channels m) (h : m ≤ D)
    (x : α → I → E4) (v : α → Labels S d) (o : α → E4) (z : α → S.Field D)
    (actual : α → Fin U.size → ℂ) (scale : α → E)
    (ordinaryOPE : ∀ i, (fun a => actual a i -
      witnessAt S D (U.listen i) (R.packet D (x a) (v a) (o a))) =o[l] scale)
    (completeProductMatch : ∀ i, (fun a => actual a i -
      witnessAt S D (U.listen i) (z a)) =o[l] scale) :
    (fun a => R.coef m j (x a) (v a) (o a) - coordinate R m D j (z a)) =o[l] scale := by
  let f : α → S.Field D := fun a => R.packet D (x a) (v a) (o a) - z a
  have hf : f =o[l] scale := by
    apply FixedHorizonReadout.isLittleO_of_samples U f scale
    intro i
    apply ((completeProductMatch i).sub (ordinaryOPE i)).congr_left
    intro a
    dsimp only [f]
    rw [map_sub]
    ring
  let c := LinearMap.toContinuousLinearMap (coordinate R m D j)
  have hc := (c.isBigO_comp f l).trans_isLittleO hf
  have he : (fun a => c (f a)) =
      (fun a => R.coef m j (x a) (v a) (o a) - coordinate R m D j (z a)) := by
    funext a
    change coordinate R m D j (R.packet D (x a) (v a) (o a) - z a) = _
    rw [map_sub, coordinate_packet R m D j h]
  rw [he] at hc
  exact hc

end YM.Integration.ReaderFiniteExtraction
