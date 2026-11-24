import YM.Integration.ActualOriginalFiniteCoefficients
import YM.Integration.ActualOrbLeadingIR

/-! Exact original-frame identification of the complete finite inversion
coefficients. The native Dictionary is expanded in the retained Run's own
label frame. Its support fixes each actual slot rank; the original engineering
factor and the one complete Orb denominator are retained at every order.

No infrared estimate or replacement of the physical measure is asserted. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualOriginalOrbitCoefficients

open Function Lattice Wilson Source
open PhysicalNext.Repeat.Legato
open XSpace FVA2
open scoped Classical BigOperators ContDiff

private theorem expand_real_combination
    {E J K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype J] [Fintype K] (b : Module.Basis K ℝ E)
    (a : J → ℝ) (f : J → E → ℝ)
    (hf : ∀ j, ContDiffAt ℝ ∞ (f j) 0) :
    Taylor.expandTaylor b (Complex.ofRealCLM ∘ (∑ j, a j • f j)) =
      ∑ j, (a j : ℂ) • Taylor.expandTaylor b (Complex.ofRealCLM ∘ f j) := by
  have hc (j : J) : ContDiffAt ℝ ∞ (Complex.ofRealCLM ∘ f j) 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (hf j)
  have he : Complex.ofRealCLM ∘ (∑ j, a j • f j) =
      ∑ j, (a j : ℂ) • (Complex.ofRealCLM ∘ f j) := by
    funext x
    simp only [Function.comp_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Complex.ofRealCLM_apply, Complex.ofReal_sum,
      Complex.ofReal_mul]
  rw [he]
  apply PowerSeries.ext
  intro k
  apply Taylor.from_real b
  intro x
  simp only [map_sum, PowerSeries.coeff_smul, map_smul,
    Taylor.expand_coeff, Taylor.divided_eval]
  rw [iteratedFDeriv_sum_apply
    (f := fun j => (a j : ℂ) • (Complex.ofRealCLM ∘ f j)) (fun j _ =>
    ((hc j).const_smul (a j : ℂ)).of_le (WithTop.coe_le_coe.mpr le_top)),
    _root_.sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [iteratedFDeriv_const_smul_apply
    ((hc j).of_le (WithTop.coe_le_coe.mpr le_top)), _root_.smul_apply]
  simp only [smul_eq_mul]
  ring

private theorem stencil_combination {G : Gauge} {P : Period}
    (T : P.Tree) {J : Type*} [Fintype J]
    (a : J → ℝ) (O : J → Config G P.side → ℝ)
    (hO : ∀ j, PertExtension.Orb.PreTest (O j)) :
    BareOrb.stencil T (∑ j, a j • O j) =
      ∑ j, (a j : ℂ) • BareOrb.stencil T (O j) := by
  have he : (∑ j, a j • O j) ∘ T.links =
      ∑ j, a j • (O j ∘ T.links) := by
    funext x
    simp only [Function.comp_apply, Finset.sum_apply, Pi.smul_apply]
  unfold BareOrb.stencil TreeFormal.enter
  rw [he]
  exact expand_real_combination (T.basis G) a (fun j => O j ∘ T.links)
    (fun j => OrbGerm.tree T (hO j))

private theorem stencil_scale {G : Gauge} {P : Period}
    (T : P.Tree) (a : ℝ) (O : Config G P.side → ℝ)
    (hO : PertExtension.Orb.PreTest O) :
    BareOrb.stencil T (a • O) = (a : ℂ) • BareOrb.stencil T O := by
  simpa only [Fintype.sum_unique] using
    stencil_combination T (fun _ : Unit => a) (fun _ : Unit => O) (fun _ => hO)

private theorem field_combination {G : Gauge}
    (R : Run G) (B : MS.Local.Physical.Deck G) (N p d q : ℕ)
    (i : B.BIndex (d : ℤ) q) (x : Site (R.family.side N p))
    (U : Config G (R.family.side N p)) :
    (∑ j, ActualOriginalDictionary.weight R B d q i j *
      physicalInversionObservable R.family N p d x j U) =
    ((R.family.S.a N) ^ d)⁻¹ *
      (((ActualOriginalDictionary.dictionary R B).cylinder d q i).O
        (R.family.side N p) x U) := by
  rw [ActualOriginalDictionary.cylinder_observable, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [ActualFiniteStencil.retained_inversion]
  ring

private theorem finite_product_combination
    {A E : Type*} [Fintype A] [DecidableEq A]
    {J : A → Type*} [∀ i, Fintype (J i)]
    (w : (i : A) → J i → ℝ) (f : (i : A) → J i → E → ℝ)
    (a : A → ℝ) (g : A → E → ℝ)
    (h : ∀ i y, ∑ j, w i j * f i j y = a i * g i y) :
    (∑ b : (i : A) → J i, (∏ i, w i (b i)) • (∏ i, f i (b i))) =
      (∏ i, a i) • (∏ i, g i) := by
  funext y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.prod_apply]
  calc
    _ = ∑ b : (i : A) → J i, ∏ i, w i (b i) * f i (b i) y := by
      simp only [Finset.prod_mul_distrib]
    _ = ∏ i, ∑ j, w i j * f i j y :=
      (Fintype.prod_sum (ι := A) (κ := J) (R := ℝ)
        (fun i j => w i j * f i j y)).symm
    _ = ∏ i, a i * g i y := Finset.prod_congr rfl fun i _ => h i y
    _ = _ := by rw [Finset.prod_mul_distrib]

variable {G : Gauge} {I : Type} [Fintype I] [LinearOrder I]
    (R : Run G) (B : MS.Local.Physical.Deck G)
    (degree rank : I → ℕ)
    (label : (i : I) → B.BIndex (degree i : ℤ) (rank i))

/-- Literal coordinates of the same native Dictionary fields in the original
Run's retained frame, with no new lift or label choice. -/
def columns : (i : I) → R.family.label (degree i) :=
  fun i => ActualOriginalDictionary.coordinates R B (degree i) (rank i) (label i)

variable (N p : ℕ) (x : I → Cover)

/-- Equality of the full functions on the original finite configuration space.
The original calibrated basis carries exactly the inverse engineering factor. -/
theorem full_observable :
    (∑ b : ActualLeadingIR.Choices R.family degree,
      (∏ i, ActualOriginalDictionary.weight R B (degree i) (rank i) (label i) (b i)) •
        physicalInversionProduct R.family N p degree
          (wrap (R.family.side N p) ∘ x) b Finset.univ) =
    (ActualLeadingIR.engineeringScale R.family degree N)⁻¹ •
      ActualOriginalFiniteCoefficients.joint R B degree rank label N p Finset.univ
        (wrap (R.family.side N p) ∘ x) := by
  unfold physicalInversionProduct ActualOriginalFiniteCoefficients.joint
    ActualLeadingIR.engineeringScale
  rw [← Finset.prod_inv_distrib]
  apply finite_product_combination
  intro i U
  exact field_combination R B N p (degree i) (rank i) (label i)
    ((wrap (R.family.side N p) ∘ x) i) U

private theorem joint_pretest :
    PertExtension.Orb.PreTest
      (ActualOriginalFiniteCoefficients.joint R B degree rank label N p Finset.univ
        (wrap (R.family.side N p) ∘ x)) := by
  apply FVAAlt2.Fixed.preT Finset.univ
    (ActualOriginalFiniteCoefficients.side_admissible R N p)
  · intro i
    exact ActualOriginalFVAAltLibrary.original_atom R B (degree i) (rank i) (label i)
      (R.family.side N p) (wrap (R.family.side N p) (x i))
  · intro i _
    exact ((ActualOriginalDictionary.dictionary R B).cylinder
      (degree i) (rank i) (label i)).continuous _ _

private theorem mixed_source
    (T : (ActualLeadingIR.actualPeriod R.family N p).Tree) :
    (∏ i, ∑ j, columns R B degree rank label i j •
      ActualLeadingSeries.source R.family N p (degree i) T
        (wrap (R.family.side N p) (x i)) j) =
    (((ActualLeadingIR.engineeringScale R.family degree N)⁻¹ : ℝ) : ℂ) •
      BareOrb.stencil T
        (ActualOriginalFiniteCoefficients.joint R B degree rank label N p Finset.univ
          (wrap (R.family.side N p) ∘ x)) := by
  rw [Fintype.prod_sum]
  have he :
      (∑ b : ActualLeadingIR.Choices R.family degree,
        ∏ i, columns R B degree rank label i (b i) •
          ActualLeadingSeries.source R.family N p (degree i) T
            (wrap (R.family.side N p) (x i)) (b i)) =
      ∑ b : ActualLeadingIR.Choices R.family degree,
        ((∏ i, ActualOriginalDictionary.weight R B (degree i) (rank i) (label i) (b i) : ℝ) : ℂ) •
          BareOrb.stencil T (physicalInversionProduct R.family N p degree
            (wrap (R.family.side N p) ∘ x) b Finset.univ) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.prod_smul,
      ActualOrbLeadingIR.source_product_stencil R.family N p degree x b R.makes]
    congr 1
    simp only [Complex.ofReal_prod, columns, ActualOriginalDictionary.weight_cast]
  rw [he, ← stencil_combination T
    (fun b : ActualLeadingIR.Choices R.family degree =>
      ∏ i, ActualOriginalDictionary.weight R B (degree i) (rank i) (label i) (b i))
    (fun b => physicalInversionProduct R.family N p degree
      (wrap (R.family.side N p) ∘ x) b Finset.univ)
    (fun b => physicalInversionProduct_pretest R.family N p degree
      (wrap (R.family.side N p) ∘ x) b R.makes Finset.univ)]
  exact (congrArg (BareOrb.stencil T)
    (full_observable R B degree rank label N p x)).trans
      (stencil_scale T _ _ (joint_pretest R B degree rank label N p x))

omit [LinearOrder I] in
private theorem mixed_restore
    (T : (ActualLeadingIR.actualPeriod R.family N p).Tree) :
    PowerSeries.X ^ (∑ i, rank i) *
      ActualLeadingSeries.series R.family N p degree T x
        (columns R B degree rank label) =
    Bare.normalized T G (∏ i, ∑ j, columns R B degree rank label i j •
      ActualLeadingSeries.source R.family N p (degree i) T
        (wrap (R.family.side N p) (x i)) j) := by
  have hi (i : I) :
      PowerSeries.X ^ rank i *
        (∑ j, columns R B degree rank label i j •
          ActualLeadingSeries.lowerFilm ((R.family.labels.level (degree i)).grades j).2
            (ActualLeadingSeries.source R.family N p (degree i) T
              (wrap (R.family.side N p) (x i)) j)) =
      ∑ j, columns R B degree rank label i j •
        ActualLeadingSeries.source R.family N p (degree i) T
          (wrap (R.family.side N p) (x i)) j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : (R.family.labels.level (degree i)).grades j = (degree i, rank i)
    · have hs := ActualLeadingSeries.source_restore R.family N p (degree i)
        (CoefficientBridge.run_valuation R (degree i)) T
        (wrap (R.family.side N p) (x i)) j
      simp only [h] at hs ⊢
      rw [mul_smul_comm, mul_comm (PowerSeries.X ^ rank i), hs]
    · have hz := ActualOriginalDictionary.off_grade R B (degree i) (rank i)
        (label i) j h
      simp only [columns, hz, zero_smul, mul_zero]
  rw [ActualLeadingSeries.series, ← Bare.normalized_scalar]
  congr 1
  rw [Bare.scalar, map_pow, PowerSeries.map_X,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => hi i

/-- The full original orbit series, after restoring the true total slot
power, is the same normalized finite Orb series of the full Dictionary product. -/
theorem restored_series :
    PowerSeries.X ^ (∑ i, rank i) *
      ActualOrbLeadingIR.orbitSeries R.family N p degree x
        (columns R B degree rank label) =
    ((ActualLeadingIR.engineeringScale R.family degree N)⁻¹ : ℂ) •
      TaylorWick.into (PowerSeries.mk (PertExtension.Orb.diag
        (PertExtension.Orb.restrictedO
          (ActualOriginalFiniteCoefficients.joint R B degree rank label N p Finset.univ
            (wrap (R.family.side N p) ∘ x))))) := by
  let T := (ActualLeadingIR.actualPeriod R.family N p).standardTree
  rw [← ActualOrbLeadingIR.series_eq_orbitSeries R.family N p degree x R.makes
    (fun i => CoefficientBridge.run_valuation R (degree i)) T,
    mixed_restore R B degree rank label N p x T,
    mixed_source R B degree rank label N p x T,
    map_smul, BareOrb.diagram_eq T (joint_pretest R B degree rank label N p x)]
  rw [Complex.ofReal_inv]
  rfl

/-- Every original RG coefficient, with its exact engineering normalization,
is the already-identified finite coefficient used by the native MS dictionary. -/
theorem coefficient (k : ℕ) :
    (ActualLeadingIR.engineeringScale R.family degree N : ℂ) *
      PowerSeries.coeff k
        (ActualOrbLeadingIR.orbitSeries R.family N p degree x
          (columns R B degree rank label)) =
    (ActualOriginalFiniteCoefficients.coefficients R B degree rank label N p Finset.univ
      (wrap (R.family.side N p) ∘ x) k : ℂ) := by
  have h := congrArg (PowerSeries.coeff (k + ∑ i, rank i))
    (restored_series R B degree rank label N p x)
  rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel,
    PowerSeries.coeff_smul] at h
  simp only [TaylorWick.into, PowerSeries.coeff_map, PowerSeries.coeff_mk,
    smul_eq_mul] at h
  change _ = (ActualLeadingIR.engineeringScale R.family degree N : ℂ)⁻¹ *
    (ActualOriginalFiniteCoefficients.coefficients R B degree rank label N p Finset.univ
      (wrap (R.family.side N p) ∘ x) k : ℂ) at h
  rw [h, ← mul_assoc, mul_inv_cancel₀, one_mul]
  exact Complex.ofReal_ne_zero.mpr
    (ActualLeadingIR.engineeringScale_pos R.family degree N).ne'

/-- Equality of the complete coefficient arrays, not only their leading or
second-order terms. Each field and the denominator are the original ones. -/
theorem series :
    (ActualLeadingIR.engineeringScale R.family degree N : ℂ) •
      ActualOrbLeadingIR.orbitSeries R.family N p degree x
        (columns R B degree rank label) =
    PowerSeries.map Complex.ofRealHom
      (PowerSeries.mk (ActualOriginalFiniteCoefficients.coefficients
        R B degree rank label N p Finset.univ
          (wrap (R.family.side N p) ∘ x))) := by
  apply PowerSeries.ext
  intro k
  simpa only [PowerSeries.coeff_smul, smul_eq_mul,
    PowerSeries.coeff_map, PowerSeries.coeff_mk, Complex.ofRealHom_eq_coe] using
      coefficient R B degree rank label N p x k


/-- The native finite RG10 feed reads the very same original RG06/08 source
family, at the exact shifted order and with the complete vacuum unchanged. -/
theorem RG10_coefficient (k : ℕ) :
    let he := even_iff_two_dvd.mpr
      (ActualOriginalFiniteCoefficients.side_admissible R N p).2
    PowerSeries.coeff (k + ∑ i, rank i)
      ((FormalOPE.RG10.InversionTop.feed he).step
        (FormalOPE.RG10.InversionTop.vertices G (R.family.side N p))
        (FormalOPE.RG10.InversionTop.raw
          (PertExtension.Orb.restrictedO
            (ActualOriginalFiniteCoefficients.joint R B degree rank label
              N p Finset.univ (wrap (R.family.side N p) ∘ x))))) =
    (ActualLeadingIR.engineeringScale R.family degree N : ℂ) *
      PowerSeries.coeff k
        (ActualOrbLeadingIR.orbitSeries R.family N p degree x
          (columns R B degree rank label)) := by
  rw [coefficient R B degree rank label N p x k]
  simpa only [ActualOriginalFiniteCoefficients.slotOrder] using
    ActualOriginalFiniteCoefficients.RG10_coefficient
      R B degree rank label N p Finset.univ (wrap (R.family.side N p) ∘ x) k

end YM.Integration.ActualOriginalOrbitCoefficients
end
