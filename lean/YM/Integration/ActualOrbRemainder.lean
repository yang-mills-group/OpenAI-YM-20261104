import YM.Integration.RunOrbLeadingIR

/-! Small-coupling remainders for the original normalized inversion quotient.
The regulator and insertion positions are fixed.  The constant and coupling
neighborhood are chosen before every independent vector of source coefficients.
No uniform infrared bound or identification with the full history is asserted. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualOrbRemainder
open Function Filter Lattice Wilson PowerSeries
open RG06 RG06.WilsonCompiler XSpace
open PertExtension PertExtension.Series PertExtension.Series.Tested
open FVA2 ActualLeadingIR ActualLeadingSeries
open scoped BigOperators Classical Topology

variable {G : Gauge} (C : Family G) (N p : ℕ)
    {I : Type*} [Fintype I] (degree : I → ℕ) (x : I → Cover)

/-- Exactly the total original coupling degree of the selected columns. -/
def slots (b : Choices C degree) : ℕ :=
  ∑ i, ((C.labels.level (degree i)).grades (b i)).2

/-- One original product, divided by the one original vacuum and then by
its proved original coupling degree. -/
def basisQuotient (b : Choices C degree) (g : ℝ) : ℝ :=
  (g⁻¹) ^ slots C degree b * Orb.preExpectation
    (physicalInversionProduct C N p degree (wrap (C.side N p) ∘ x) b Finset.univ) g

def basisCoefficients (b : Choices C degree) (k : ℕ) : ℝ :=
  Orb.diag (Orb.restrictedO
    (physicalInversionProduct C N p degree (wrap (C.side N p) ∘ x) b Finset.univ))
      (slots C degree b + k)

/-- Independent source mixtures keep the original product and common
vacuum in every term. Different original grades are lowered separately. -/
def quotient (v : (i : I) → C.label (degree i)) (g : ℝ) : ℂ :=
  ∑ b : Choices C degree, (∏ i, v i (b i)) * (basisQuotient C N p degree x b g : ℂ)

theorem coefficients (v : (i : I) → C.label (degree i)) (k : ℕ) :
    coeff k (ActualOrbLeadingIR.orbitSeries C N p degree x v) =
      ∑ b : Choices C degree, (∏ i, v i (b i)) *
        (basisCoefficients C N p degree x b k : ℂ) := by
  simp only [ActualOrbLeadingIR.orbitSeries, map_sum, map_smul, smul_eq_mul,
    FormalOPE.RG10.lower, coeff_mk, TaylorWick.into_coeff,
    basisCoefficients, slots]

private theorem polynomial (v : (i : I) → C.label (degree i)) (k : ℕ) (g : ℝ) :
    peval (fun j => coeff j (ActualOrbLeadingIR.orbitSeries C N p degree x v)) k g =
      ∑ b : Choices C degree, (∏ i, v i (b i)) *
        ((peval (basisCoefficients C N p degree x b) k g : ℝ) : ℂ) := by
  simp only [peval, Zone.eval, coefficients, Finset.smul_sum, smul_eq_mul,
    Complex.real_smul, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem remainder_expansion (v : (i : I) → C.label (degree i))
    (k : ℕ) (g : ℝ) :
    quotient C N p degree x v g -
      peval (fun j => coeff j (ActualOrbLeadingIR.orbitSeries C N p degree x v)) k g =
      ∑ b : Choices C degree, (∏ i, v i (b i)) *
        ((basisQuotient C N p degree x b g -
          peval (basisCoefficients C N p degree x b) k g : ℝ) : ℂ) := by
  rw [quotient, polynomial, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [Complex.ofReal_sub, mul_sub]

private theorem even : Even (C.side N p).val := by
  obtain ⟨q, hq⟩ := C.S.side_four N p
  change (C.side N p).val = 4 * q at hq
  exact ⟨2 * q, by omega⟩

/-- Native asymptotics are shifted only after the original valuation has
proved that every lower coefficient vanishes. -/
theorem basis_asymptotic (hC : C.Makes)
    (hV : ∀ i, Bid.pop (C.localSection (degree i)))
    (T : (actualPeriod C N p).Tree) (b : Choices C degree) :
    Aspiration (basisQuotient C N p degree x b)
      (basisCoefficients C N p degree x b) := by
  let O := physicalInversionProduct C N p degree
    (wrap (C.side N p) ∘ x) b Finset.univ
  have hO : Orb.PreTest O :=
    physicalInversionProduct_pretest C N p degree
      (wrap (C.side N p) ∘ x) b hC Finset.univ
  have hz (j : ℕ) (hj : j < slots C degree b) :
      Orb.diag (Orb.restrictedO O) j = 0 := by
    have he := congrArg (coeff j)
      (ActualOrbLeadingIR.basis_orbit C N p degree x b hC hV T)
    change j < ∑ i, ((C.labels.level (degree i)).grades (b i)).2 at hj
    rw [coeff_X_pow_mul', if_neg hj.not_ge, TaylorWick.into_coeff, coeff_mk] at he
    exact_mod_cast he.symm
  have h := (Orb.before_tree_formula (even C N p) (Orb.traySpec G) hO).shift hz
  exact h

/-- One constant and one positive-coupling neighborhood work for all
independent source vectors at this fixed regulator, placement and order. -/
theorem uniform_remainder (hC : C.Makes)
    (hV : ∀ i, Bid.pop (C.localSection (degree i)))
    (T : (actualPeriod C N p).Tree) (k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ g in Tested.germ,
      ∀ v : (i : I) → C.label (degree i),
        ‖quotient C N p degree x v g -
          peval (fun j => coeff j (ActualOrbLeadingIR.orbitSeries C N p degree x v)) k g‖ ≤
          A * g ^ (k + 1) * inputMass C degree v := by
  choose A hA H using fun b : Choices C degree =>
    basis_asymptotic C N p degree x hC hV T b k
  let B : ℝ := ∑ b, A b
  have hB : 0 ≤ B := Finset.sum_nonneg fun b _ => hA b
  have hAB (b : Choices C degree) : A b ≤ B :=
    Finset.single_le_sum (fun c _ => hA c) (Finset.mem_univ b)
  refine ⟨B, hB, ?_⟩
  filter_upwards [eventually_all.mpr H, Tested.eventually_pos] with g hg hp
  intro v
  rw [remainder_expansion]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ b : Choices C degree, (∏ i, ‖v i (b i)‖) * (B * g ^ (k + 1)) := by
      apply Finset.sum_le_sum
      intro b _
      rw [norm_mul, norm_prod, Complex.norm_real]
      apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      exact (hg b).trans (mul_le_mul_of_nonneg_right (hAB b) (pow_nonneg hp.le _))
    _ = B * g ^ (k + 1) * inputMass C degree v := by
      rw [← Finset.sum_mul]
      have he : (∑ b : Choices C degree, ∏ i, ‖v i (b i)‖) = inputMass C degree v :=
        (Fintype.prod_sum (fun i j => ‖v i j‖)).symm
      rw [he, mul_comm]

/-- The same estimate reads the already-identified full source series. -/
theorem source_remainder (hC : C.Makes)
    (hV : ∀ i, Bid.pop (C.localSection (degree i)))
    (T : (actualPeriod C N p).Tree) (k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ g in Tested.germ,
      ∀ v : (i : I) → C.label (degree i),
        ‖quotient C N p degree x v g -
          peval (fun j => coeff j (ActualLeadingSeries.series C N p degree T x v)) k g‖ ≤
          A * g ^ (k + 1) * inputMass C degree v := by
  simpa only [ActualOrbLeadingIR.series_eq_orbitSeries C N p degree x hC hV T] using
    uniform_remainder C N p degree x hC hV T k

end YM.Integration.ActualOrbRemainder

namespace YM.Integration.RunOrbRemainder
open Lattice Wilson Filter PowerSeries PertExtension.Series
open RG06 RG06.WilsonCompiler XSpace ActualLeadingIR ActualLeadingSeries
open PhysicalNext.Repeat.Legato
open scoped Classical Topology

/-- The retained Run supplies construction and valuation. Constants may
depend on its fixed regulator and positions, but never on the test vectors. -/
theorem uniform_remainder {G : Gauge} (R : Run G) (N p : ℕ)
    {I : Type*} [Fintype I] (degree : I → ℕ) (x : I → Cover)
    (T : (actualPeriod R.family N p).Tree) (k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ g in Tested.germ,
      ∀ v : (i : I) → R.family.label (degree i),
        ‖ActualOrbRemainder.quotient R.family N p degree x v g -
          Tested.peval (fun j => coeff j
            (ActualOrbLeadingIR.orbitSeries R.family N p degree x v)) k g‖ ≤
          A * g ^ (k + 1) * inputMass R.family degree v :=
  ActualOrbRemainder.uniform_remainder R.family N p degree x R.makes
    (fun i => CoefficientBridge.run_valuation R (degree i)) T k

end YM.Integration.RunOrbRemainder
