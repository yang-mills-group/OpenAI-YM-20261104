import YM.PertExtension.GaussianIBP
import YM.Next.RANK.Common
/-!
# The independent pairing operation

Use Rank.Normal.blend on the inverse precision; no need for a positive
form on the leg index space. Result proves equality to the *ordinary*
normalized complex Gaussian polynomial moment with Hessian in real counting
units. Include Jacobian factors on vertices separately (even in tree gauge).
No estimates under changing the regulator are implied. We do NOT import a
result about the stochastic tag law from another prescription or gauge.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Wick
open MeasureTheory MvPolynomial Finset Filter YM.PertExtension
open GaussianScore Next.Rank Next.Rank.Normal
open scoped BigOperators Classical
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def coloring (Γ : Law E) (ℓ : W → Module.Dual ℝ E) : Normal.Symmetric W := by
  refine ⟨fun i j => Complex.ofReal (Γ.wick (ℓ i) (ℓ j)),fun i j => ?_⟩
  apply congr_arg
  change ℓ j _=ℓ i _
  nth_rw 1 [← Γ.applies (ℓ j)]
  rw [Γ.turns,Γ.applies]

def charge (Γ : Law E) (ℓ : W → Module.Dual ℝ E) : poly W →ₗ[ℂ] ℂ := blend (coloring Γ ℓ) 0

theorem charge_one (Γ : Law E) (ℓ : W → Module.Dual ℝ E) : charge Γ ℓ 1=1 := fresh _ _

def paint (ℓ : W → Module.Dual ℝ E) (p : poly W) (x : E) : ℂ :=
  aeval (fun i => Complex.ofReal (ℓ i x)) p

variable [MeasurableSpace E][BorelSpace E] (Γ : Law E) (μ : Measure E) [μ.HasTemperateGrowth]

/-- Discard this positive scalar only in a conditional normalization,
not in the unnormalized determinant Jacobian. -/
def mass := ∫ x, Γ.kern x ∂μ
include μ
lemma mass_pos [NeZero μ] : 0 < mass Γ μ := by
  have hi := Γ.integrable_entry (A:=1) μ (Series.Zone.Invoice.const (1:ℝ)) continuous_const
  rw [one_mul] at hi
  exact integral_exp_pos hi

def normed (f : E → ℂ) := (∫ x, f x * Complex.ofReal (Γ.kern x) ∂μ) / Complex.ofReal (mass Γ μ)

lemma hue_glyph {I : Type*} (ℓ : W → Module.Dual ℝ E)(i : I → W) (s : Finset I) :
    Integrable (fun x : E => paint ℓ (glyphs i s) x * Complex.ofReal (Γ.kern x)) μ := by
  have he x : paint ℓ (glyphs i s) x = Complex.ofReal (Law.product (ℓ ∘ i) s x) := by
    simp [paint,Law.product,glyphs,Complex.ofReal_prod]
  simp_rw [he,← Complex.ofReal_mul]; exact (Γ.integrable_entry μ (Law.product_bound ..) (Law.product_cont ..)).ofReal

lemma paint_integrable (ℓ : W → Module.Dual ℝ E) (p : poly W) :
    Integrable (fun x : E => paint ℓ p x * Complex.ofReal (Γ.kern x)) μ := by
  classical
  rw [p.as_sum]; simp_rw [paint,map_sum,Finset.sum_mul]
  apply MeasureTheory.integrable_finsetSum; intro i _
  obtain ⟨v,hv⟩ := Common.letter i
  have hu : monomial i (coeff i p)= (coeff i p) • glyphs v univ := by rw [← hv,← map_smul,smul_eq_mul,mul_one]
  simp_rw [hu,map_smul,smul_eq_mul,mul_assoc]; exact (hue_glyph Γ μ ℓ v _).const_mul _

variable [μ.IsAddRightInvariant][NeZero μ]

lemma merge_one {I : Type*} (ℓ : W → Module.Dual ℝ E)(i : I → W) (s : Finset I) :
    Complex.ofReal (Γ.average μ (Law.product (ℓ ∘ i) s)) = charge Γ ℓ (glyphs i s) := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    obtain rfl|⟨a,ha⟩ := s.eq_empty_or_nonempty
    · simp only [glyphs,prod_empty,charge_one]
      rw [show Law.product _ ∅=1 from funext fun x=>prod_empty, Γ.empty, Complex.ofReal_one]
    let t := s.erase a
    have H : s=insert a t := (insert_erase ha).symm
    have ha' : a∉t := notMem_erase a s
    have hk : Law.product (ℓ ∘ i) s = fun x => Law.product (ℓ ∘ i) t x * ℓ (i a) x := by
      funext x; unfold Law.product; nth_rw 1 [H]; rw [prod_insert ha',mul_comm]; rfl
    rw [hk,Γ.recursion,charge];
    conv_rhs => rw [H,spring _ _ i t ha']
    rw [Complex.ofReal_sum,Pi.zero_apply,zero_mul,zero_add]
    exact sum_congr rfl fun j _ => by
      have ht := ih (t.erase j) (Finset.ssubset_of_subset_of_ssubset (erase_subset ..) (erase_ssubset ha))
      rw [Complex.ofReal_mul,ht,mul_comm]; rfl

theorem analytic_pairing (ℓ : W → Module.Dual ℝ E)(p : poly W) :
    normed Γ μ (paint ℓ p) = charge Γ ℓ p := by
  classical
  have hh {I : Type} (v : I → W) (s : Finset I) : normed Γ μ (paint ℓ (glyphs v s))= charge Γ ℓ (glyphs v s) := by
    rw [← merge_one Γ μ ℓ v s,Law.average, normed,Complex.ofReal_div]
    unfold mass; congr 1
    refine Eq.trans ?_ (integral_ofReal (𝕜:=ℂ) (μ:=μ) (f:=Law.product (ℓ ∘ v) s*Γ.kern))
    apply integral_congr_ae (Eventually.of_forall fun x => ?_);
    simp [paint,glyphs,Law.product,Complex.ofReal_prod]
  rw [p.as_sum]; unfold normed; simp_rw [paint,map_sum,sum_mul]
  rw [integral_finsetSum, Finset.sum_div]
  · apply sum_congr rfl
    intro i hi
    obtain ⟨v,hv⟩ := Common.letter i
    have he : monomial i (coeff i p) = (coeff i p) • glyphs v univ := by rw [← hv,← map_smul,smul_eq_mul,mul_one]
    simp_rw [he,map_smul,smul_eq_mul,mul_assoc]
    rw [integral_const_mul,mul_div_assoc]; rw [← hh]
    rfl
  intro i _; exact paint_integrable Γ μ _ _

end YM.RG02.Wick
