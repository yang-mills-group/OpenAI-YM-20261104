import YM.Integration.ActualRunStartupIdentity
import YM.Integration.HorizonPhysicalFields

/-! Literal startup on the retained Run, and the exact cost of its original
physical top input. The full Wilson residual, engineering scaling, threshold
scaling and inverse terminal map remain explicit. The section constant is
uniform over tori; the actual coordinate cost is not claimed uniform in N,p.
No vacuum division or replacement input is introduced. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunStartupInput

open Function Finset Lattice Wilson RG Source Labels
open PhysicalNext.Repeat.Legato
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) (T : Campaign R)
include T

theorem represented_path (N p : ℕ) :
    (R.family.path.rep N p N).path =
      WilsonStartup.Design.top G (R.family.path.levels.params N).clip := by
  have h := ((R.T.sticks N p).prices N (Nat.zero_le N) (Nat.le_refl N)).1.path
  exact h.trans ((congr_fun (congr_fun R.alloy.B.bases N) N).trans
    (ActualRunStartupIdentity.initial_path R T N))

theorem ell (N p : ℕ) (U : Config G (R.family.side N p))
    (b : WilsonStartup.Cell (R.family.side N p)) :
    (R.family.path.rep N p N).path.ell U b =
      WilsonStartup.Design.sideRoot (R.family.path.levels.params N).clip •
        G.curvature (faceValue U b) := by
  rw [represented_path R T]
  exact WilsonStartup.Design.ell_top _ _ _

/-- The actual top principal action, including its complete residual. -/
theorem principal (N p : ℕ) (U : Config G (R.family.side N p)) :
    Precision.quadratic (R.family.path.rep N p N).clip (R.family.path.rep N p N).path U +
      Precision.uncut (R.family.path.rep N p N).path.cubic U +
      Precision.uncut (R.family.path.rep N p N).path.quartic U +
      (∑ b : WilsonStartup.Cell (R.family.side N p),
        WilsonStartup.Design.bulk (R.family.path.rep N p N).clip *
          WilsonStartup.residual G b U) = energy U := by
  have hclip : (R.family.path.rep N p N).clip =
      (R.family.path.levels.params N).clip :=
    (R.makes.wilson.represents N p N le_rfl).clip
  rw [hclip, represented_path R T]
  exact WilsonStartup.Design.principal_top _ U
    (Push.PriceCompiler.Canonical.direct_le_one
      (R.alloy.B.support.cap N N le_rfl).metric)

omit T

/-- This is the full inserted top density, with its original scale and
vacuum factor. The physical observable itself is not divided by a vacuum. -/
theorem inserted_density (d N p : ℕ) (v : R.family.label d)
    (hN : R.family.ref d ≤ N) (U : Config G (R.family.side N p)) :
    ((R.family.factory d N p).entries N
      ((R.family.factory d N p).terminal.symm v)).density 0
      (R.family.localSection d) (R.family.path.rep N p N) U =
      ((R.family.S.a N : ℂ)^d) * (bare (R.family.beta N p) U : ℂ) *
        R.family.O N p v 0 U := by
  have h : ((R.family.factory d N p).entries N
      ((R.family.factory d N p).terminal.symm v)).density 0
      (R.family.localSection d) (R.family.path.rep N p N) U =
      ((R.family.S.a N : ℂ)^d) * ((R.family.path.rep N p N).eval U : ℂ) *
        R.family.O N p v 0 U :=
    (R.makes.calibrated d N p hN).encode
      ((R.family.factory d N p).terminal.symm v) U
  have he : (R.family.path.rep N p N).eval = bare (R.family.beta N p) :=
    (R.makes.wilson.starts N p).2
  rw [he] at h
  exact h

/-- The exact finite coordinate cost includes both original scaling factors
and the genuine inverse terminal map. -/
def physicalCost (d N p : ℕ) (v : R.family.label d) : ℝ :=
  (R.family.labels.level d).coeffSize
    (HorizonPhysicalFields.rawCoordinates R.family N p d v)

theorem physical_cost_explicit (d N p : ℕ) (v : R.family.label d) :
    physicalCost R d N p v = (R.family.S.a N ^ d)⁻¹ *
      ∑ i : (R.family.labels.level d).Index,
        (R.family.path.levels.clock.threshold N ^
          ((R.family.labels.level d).grades i).2)⁻¹ *
          ‖((R.family.factory d N p).terminal.symm v) i‖ := by
  unfold physicalCost HorizonPhysicalFields.rawCoordinates
    ActualPhysicalCoordinates.coordinates
  rw [Extra.Histories.Size.smul, norm_inv, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (R.family.S.a_pos N).le]
  congr 1
  unfold Frame.coeffSize
  apply Finset.sum_congr rfl
  intro i _
  have ht : 0 ≤ R.family.path.levels.clock.threshold N :=
    (R.family.path.levels.budget N).threshold_pos.le
  rw [Frame.scaled_apply, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (pow_nonneg
      (inv_nonneg.mpr ht) _), inv_pow]

/-- Compactness is used only for the fixed section on the universal cover.
The same section constant works on every torus and for every coefficient. -/
theorem section_bound (d : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : Side) (v : R.family.label d)
      (o : Site n) (U : Config G n),
      ‖(R.family.localSection d).places v o U‖ ≤
        M * (R.family.labels.level d).coeffSize v := by
  let F := R.family.labels.level d
  let S := R.family.localSection d
  have h : ∀ i : F.Index, ∃ c : ℝ, ∀ U : CoverConfig G,
      ‖S.evaluate (Extra.Histories.Size.axis F i) U‖ ≤ c := by
    intro i
    obtain ⟨c, hc⟩ := (isCompact_range
      ((S.continuous_evaluate (Extra.Histories.Size.axis F i)).norm)).bddAbove
    exact ⟨c, fun U => hc ⟨U, rfl⟩⟩
  choose c hc using h
  let M : ℝ := ∑ i : F.Index, max (c i) 0
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => le_max_right _ _
  refine ⟨M, hM, ?_⟩
  intro n v o U
  have hAxis (i : F.Index) :
      ‖S.places (Extra.Histories.Size.axis F i) o U‖ ≤ M := by
    apply (hc i (expandAt o U)).trans
    exact (le_max_left _ _).trans (Finset.single_le_sum
      (fun j _ => le_max_right (c j) 0) (Finset.mem_univ i))
  rw [HorizonPhysicalFields.section_expansion]
  calc
    _ ≤ ∑ i : F.Index, ‖v i‖ *
        ‖S.places (Extra.Histories.Size.axis F i) o U‖ := by
      simpa only [norm_mul] using
        (norm_sum_le Finset.univ (fun i : F.Index =>
          v i * S.places (Extra.Histories.Size.axis F i) o U))
    _ ≤ ∑ i : F.Index, ‖v i‖ * M := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hAxis i) (norm_nonneg _)
    _ = M * F.coeffSize v := by
      simp only [Frame.coeffSize, Finset.sum_mul, mul_comm]

/-- A genuine bound on the original, unmodified top observable. Only the
section constant is uniform; paying the displayed cost uniformly is separate. -/
theorem physical_bound (d : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (N p : ℕ) (v : R.family.label d)
      (o : Site (R.family.side N p)) (U : Config G (R.family.side N p)),
      ‖R.family.O N p v o U‖ ≤ M * physicalCost R d N p v := by
  obtain ⟨M, hM, h⟩ := section_bound R d
  refine ⟨M, hM, ?_⟩
  intro N p v o U
  rw [HorizonPhysicalFields.physical_as_section]
  exact h _ _ _ _

end YM.Integration.ActualRunStartupInput
