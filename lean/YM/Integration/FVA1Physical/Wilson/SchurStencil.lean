import YM.Integration.FVA1Physical.Wilson.StencilBound
import YM.Integration.FVA1Physical.Wilson.SchurRate

/-! The physical Schur Gaussian with a true exterior is compared on local
polynomial readings with the full inverse Hessian and an exterior-free mean. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Matrix Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Heath MSbar.Whisk MSbar.Bulk MSbar.Mosaic MSbar.Bakery.Film MSbar.Kelvin
open MSbar.Cacao Further.GaussianScalar MvPolynomial Push.Uniform Next.SectorChange RGComparison.Core16
open scoped Classical Topology
variable {G : Gauge} {σ : Type} [Fintype σ] [DecidableEq σ]

def interiorCoordinate (A : Mosaic.Issue G) (J : Voice G) (y : ℝ) (z : Positions (Primary A.c G))
    (b : Site A.f) (U : Config G A.f) :=
  him J A.F (boxY y b) (represent (tint G (Exterior.Body 1 A.c) z))
    (vest (priced A.F A.v A.pre.clip A.pre.path) z) (mold A.pre A.F A.v)
    (boxX y b) (linCash A.F z) U

def bulkCoordinate (A : Mosaic.Issue G) (z : Positions (Primary A.c G)) :=
  chair A.F (vest (priced A.F A.v A.pre.clip A.pre.path) z) (linCash A.F z)

def gaussianReading {ι : Type} [Fintype ι] [DecidableEq ι] (s : σ→ι)
    (mean : View ι) (C : Matrix ι ι ℝ) (P : Pot σ) :=
  ∫ v:View ι, MvPolynomial.eval (fun i=>mean (s i)+v (s i)) P ∂fieldLaw C

lemma gaussianReading_matrix {ι : Type} [Fintype ι] [DecidableEq ι] (s : σ→ι)
    (mean : View ι) (C : Matrix ι ι ℝ) (P : Pot σ) :
    gaussianReading s mean C P =
      ∫ v:View ι, MvPolynomial.eval (mean ∘ s + ((imbed s).transpose) *ᵥ v) P ∂fieldLaw C := by
  unfold gaussianReading; simp_rw [trimmed]; rfl

lemma gaussianReading_coeff {ι : Type} [Fintype ι] [DecidableEq ι] (s : σ→ι)
    (mean : View ι) (C : Matrix ι ι ℝ) (hp : C.PosDef) (P : Pot σ) :
    gaussianReading s mean C P =
      MvPolynomial.eval (parameters (mean ∘ s) (C.submatrix s s)) (wickStencil P) := by
  rw [gaussianReading_matrix, ←wickStencil_integral _ _ hp]
  rw [Matrix.transpose_transpose,←clipped]; rfl

theorem gaussian_read_price (P : Pot σ) :
    ∃ (A : ℝ) (d : ℕ), 0≤A ∧
    ∀ (ι ι' : Type) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (s : σ → ι) (s' : σ → ι') (x : View ι) (w : View ι')
    (C : Matrix ι ι ℝ) (D : Matrix ι' ι' ℝ),
    C.PosDef → D.PosDef → ∀ (R ε : ℝ), 1≤R → 0≤ε →
    (∀ i, |x (s i)| ≤ R) → (∀ i, |w (s' i)| ≤ R) →
    (∀ i j, |C (s i) (s j)| ≤ R) → (∀ i j, |D (s' i) (s' j)| ≤ R) →
    (∀ i, |x (s i)-w (s' i)| ≤ ε) → (∀ i j, |C (s i) (s j)-D (s' i) (s' j)| ≤ ε) →
    |gaussianReading s x C P-gaussianReading s' w D P| ≤ A*R^d*ε := by
  obtain ⟨A,d,ha,buy⟩ := wick_stencil_stability P
  refine ⟨A,d,ha,?_⟩
  intro ι ι' _ _ _ _ s t x y C D hc hd R ε hR hε first second cov other diff delta
  rw [gaussianReading_matrix,gaussianReading_matrix]
  apply buy _ _ _ _ _ _ hc hd _ _ R ε hR hε
  all_goals simp only [Matrix.transpose_transpose,←clipped]
  · rintro (i|⟨i,j⟩); exact first i; exact cov i j
  · rintro (i|⟨i,j⟩); exact second i; exact other i j
  rintro (i|⟨i,j⟩); exact diff i; exact delta i j

def interiorReading (A : Mosaic.Issue G) (J : Voice G) (y : ℝ) (z : Positions (Primary A.c G))
    (b : Site A.f) (U : Config G A.f) (s : σ → Lake A.F (boxX y b) G) (P : Pot σ) :=
  let i:=includeX (G:=G) A.F (boxX y b)
  let m:=fun a=> (A.fClock)⁻¹ * interiorCoordinate A J y z b U (i a)
  gaussianReading s m ((pinch i (mold A.pre A.F A.v))⁻¹) P

def bulkReading (A : Mosaic.Issue G) (z : Positions (Primary A.c G))
    (s : σ → Key A.F G) (P : Pot σ) :=
  gaussianReading s (fun i => (A.fClock)⁻¹ * bulkCoordinate A z i) (mold A.pre A.F A.v)⁻¹ P

lemma schur_core_entry {ι : Type} [Fintype ι] {n : Side} (l : ι→Site n)
    (M : Matrix ι ι ℝ) (e : ℝ) (i j : ι)
    (bound : (∑ k,|M i k| * liftW 0 0 (separation (l i) (l k))) ≤ e) : |M i j| ≤ e := by
  have ht : (∑ k,|M i k|) ≤ e := by simpa [liftW] using bound
  exact (Finset.single_le_sum (fun k (_ : k∈Finset.univ)=>abs_nonneg (M i k)) (Finset.mem_univ j)).trans ht

end YM.Integration.FVA1Physical.Wilson
