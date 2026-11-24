import YM.Integration.ActualStencilCylinder
import YM.Integration.OrbNormalizationLinearity
import YM.Integration.ActualOrbRemainder

/-! Exact scalar dictionary from the original calibrated observables to
their fixed unscaled cylinders. Products are formed before the single
normalized Orb prescription. This is an all-order finite-regulator identity,
not an infrared bound or a choice of a replacement MS observable. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualStencilOrb
open Function Lattice Wilson Source PowerSeries
open PertExtension ActualStencilCylinder ActualLeadingIR
open scoped BigOperators Classical ContDiff
variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}

theorem observed_pretest (S : SectionData F) {H : Hol G} (hS : S.Sound H)
    (c : F.Coeff) (x : Site n) : Orb.PreTest (observed S c n x) := by
  have hc := observed_continuous S c n x
  refine ⟨fun g _ U => congrArg Complex.re (S.placed_invariant hS x c g U),
    ⟨hc.comp Orb.continuous_links, ?_⟩, hc⟩
  exact (Complex.reCLM.contDiff.comp (section_inversion_smooth S c x)).contDiffAt

variable (C : Family G) (N p : ℕ)

theorem calibrated (d : ℕ) (i : (C.labels.level d).Index)
    (x : Site (C.side N p)) (U : Config G (C.side N p)) :
    physicalInversionObservable C N p d x i U =
      ((C.S.a N) ^ d)⁻¹ * observed (C.localSection d) (Pi.single i 1)
        (C.side N p) x U := by
  unfold physicalInversionObservable
  rw [Dict06.Actual.names, Dict06.Actual.meet, (C.labels.level d).coords_basis]
  have hf : Dict06.Actual.factor C N d =
      ((((C.S.a N) ^ d)⁻¹ : ℝ) : ℂ) := by simp [Dict06.Actual.factor]
  rw [hf]
  change (((((C.S.a N) ^ d)⁻¹ : ℝ) : ℂ) *
      (C.localSection d).places (Pi.single i 1) x U).re =
    ((C.S.a N) ^ d)⁻¹ * ((C.localSection d).places (Pi.single i 1) x U).re
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

variable {I : Type*} (degree : I → ℕ)
    (positions : I → Site (C.side N p)) (b : Choices C degree)

def rawProduct (s : Finset I) : Config G (C.side N p) → ℝ :=
  ∏ i ∈ s, observed (C.localSection (degree i)) (Pi.single (b i) 1)
    (C.side N p) (positions i)

def engineering (s : Finset I) : ℝ := ∏ i ∈ s, ((C.S.a N) ^ degree i)⁻¹

theorem rawProduct_pretest (hC : C.Makes) (s : Finset I) :
    Orb.PreTest (rawProduct C N p degree positions b s) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [rawProduct, Finset.prod_empty]
    exact ⟨fun _ _ _ => rfl, Orb.one_test, continuous_const⟩
  | @insert i s hi ih =>
    rw [rawProduct, Finset.prod_insert hi]
    have hp := observed_pretest (C.localSection (degree i)) (hC.sections (degree i))
      (Pi.single (b i) 1) (positions i)
    refine ⟨?_, ⟨hp.curved.boundedness.mul ih.curved.boundedness,
      hp.curved.germ.mul ih.curved.germ⟩, hp.continuous.mul ih.continuous⟩
    intro g hg U
    change observed (C.localSection (degree i)) (Pi.single (b i) 1)
        (C.side N p) (positions i) (Lattice.gauge g U) *
        rawProduct C N p degree positions b s (Lattice.gauge g U) =
      observed (C.localSection (degree i)) (Pi.single (b i) 1)
        (C.side N p) (positions i) U * rawProduct C N p degree positions b s U
    rw [hp.gauge g hg U, ih.gauge g hg U]

theorem product_eq (s : Finset I) :
    physicalInversionProduct C N p degree positions b s =
      fun U => engineering C N degree s * rawProduct C N p degree positions b s U := by
  funext U
  simp only [physicalInversionProduct, rawProduct, engineering, Finset.prod_apply]
  simp_rw [calibrated]
  exact Finset.prod_mul_distrib

private theorem even : Even (C.side N p).val := by
  obtain ⟨q, hq⟩ := C.S.side_four N p
  change (C.side N p).val = 4 * q at hq
  exact ⟨2 * q, by omega⟩

theorem coefficient_eq (hC : C.Makes) (s : Finset I) (k : ℕ) :
    Orb.diag (Orb.restrictedO (physicalInversionProduct C N p degree positions b s)) k =
      engineering C N degree s *
        Orb.diag (Orb.restrictedO (rawProduct C N p degree positions b s)) k := by
  rw [product_eq]
  exact OrbNormalizationLinearity.restricted_diagonal_const_mul
    (even C N p) (rawProduct_pretest C N p degree positions b hC s) _ k

variable [Fintype I] (x : I → Cover)

theorem basis_coefficients (hC : C.Makes) (k : ℕ) :
    ActualOrbRemainder.basisCoefficients C N p degree x b k =
      engineering C N degree Finset.univ *
        Orb.diag (Orb.restrictedO (rawProduct C N p degree
          (wrap (C.side N p) ∘ x) b Finset.univ))
            (ActualOrbRemainder.slots C degree b + k) :=
  coefficient_eq C N p degree (wrap (C.side N p) ∘ x) b hC Finset.univ _

/-- The engineering scalar is fixed before the arbitrary independent
source vectors, while each chosen basis product retains its own grade. -/
theorem independent_coefficients (hC : C.Makes)
    (v : (i : I) → C.label (degree i)) (k : ℕ) :
    coeff k (ActualOrbLeadingIR.orbitSeries C N p degree x v) =
      (engineering C N degree Finset.univ : ℂ) *
        ∑ b : Choices C degree, (∏ i, v i (b i)) *
          (Orb.diag (Orb.restrictedO (rawProduct C N p degree
            (wrap (C.side N p) ∘ x) b Finset.univ))
              (ActualOrbRemainder.slots C degree b + k) : ℂ) := by
  rw [ActualOrbRemainder.coefficients, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [basis_coefficients C N p degree b x hC k, Complex.ofReal_mul]
  ring

end YM.Integration.ActualStencilOrb
