import YM.Integration.WilsonSectionPrice
import YM.Integration.ActualOriginalQPointSetup
import YM.Integration.ActualOriginalFeeGrowth
import YM.Integration.FullQLocalOutputScaling

/-! Uniform clock growth for the fixed prescribed original Q field and every
independently tested point insertion, on every torus and original Wilson field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPointStartupPrice
open Function Finset MeasureTheory Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison
open IterationFour IterationFour.Vacuum FullQLocal.RenderedStep
open MergeProof MergeProof.Accent WilsonSectionPrice
open scoped Classical BigOperators Topology
variable {G : Gauge} {V : Type} {R : Run G} {B : MS.Local.Physical.Deck G}
    [DecidableEq V] [Fintype V] (Q : MS.Land.Prescription B) (u : V → MS.Rake.Label B)

/-- The fixed bare stencils in a single prescribed column. -/
def base (i : V) : ℝ :=
  ∑ g : MS.Menus.Glyph B (u i).h, price (R.family.localSection g.size)
    (ActualOriginalDictionary.coordinates R B g.size g.grade g.2.2)

omit [DecidableEq V] [Fintype V] in
private theorem base_nonneg (i : V) : 0 ≤ base (R:=R) u i :=
  Finset.sum_nonneg fun _ _ => (uniform _ _).choose_spec.1

omit [DecidableEq V] in
/-- Every shifted fee, fixed original section, link and position receives
the same polynomial bound before the physical torus and tests are chosen. -/
theorem columns (R : Run G) (K : ℕ) (μ : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ q : ℕ, ∀ (i : V) (k : ℕ), k ≤ K → ∀ t : ℝ,
      column (R:=R) Q (u i) (μ-t) k ≤ A*(1+‖t‖)^q := by
  obtain ⟨a,ha,q,hq⟩ := ActualOriginalFeeGrowth.shifted_bound B Q u K μ
  let b := ∑ i : V,base (R:=R) u i
  refine ⟨max 1 (a*b),le_max_left ..,q,?_⟩
  intro i k hk t
  have hs : base (R:=R) u i ≤ b := Finset.single_le_sum (fun i (_ : i∈(univ : Finset V)) => base_nonneg u i) (mem_univ i)
  have ht : 0 ≤ (1+‖t‖)^q := pow_nonneg (by positivity) _
  calc column (R:=R) Q (u i) (μ-t) k ≤ (a*(1+‖t‖)^q)*base (R:=R) u i := by
         unfold column base
         rw [Finset.mul_sum]
         apply Finset.sum_le_sum
         intro g _
         exact mul_le_mul_of_nonneg_right (hq i k hk g t) (uniform _ _).choose_spec.1
       _ = a*base (R:=R) u i*(1+‖t‖)^q := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hs ha.le).trans (le_max_right _ _)) ht

variable [Nonempty V]

omit [DecidableEq V] [Fintype V] [Nonempty V] in
/-- Every independent unit test of the true point datum is read at zero. -/
theorem reader (R : Run G) (J : Request V) (p L : ℕ) (o : V → Site (R.family.side L p))
    (x : IndependentTests (ActualRunQlocalNativeTuple.orbit (ActualOriginalQPointSetup.pointDatum R J p L o))) (i : V) :
    ‖ActualRunQlocalNativeTuple.reader (ActualOriginalQPointSetup.pointDatum R J p L o) i
      (testInclusion _ x i)‖ ≤ 1 := by
  let D := ActualOriginalQPointSetup.pointDatum R J p L o
  have he : ActualRunQlocalNativeTuple.reader D i (testInclusion _ x i) = (x i).val 0 :=
    ActualOriginalQPointDatum.reader_eq R p L o (fun i => (J.tests i).D) (fun _ => 0) i (testInclusion _ x i)
  rw [he]
  have h := (x i).property.limits 0 (Nat.zero_le _) 0 (ComparisonDensity.Address.Orbit.dawn _)
  simpa only [norm_iteratedFDeriv_zero,ComparisonDensity.Address.Orbit.flat,one_mul] using h

omit [Nonempty V] in
/-- All native point-test products obey one polynomial, uniformly in cutoff,
period, roots, link field and independently purchased tests. -/
theorem product (R : Run G) (J : Request V) (K : ℕ) (μ : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ q : ℕ, ∀ (m p : ℕ) (o : V → Site (R.family.side (m+1) p))
      (t : ℝ) (orders : V → ℕ), (∀ i, orders i ≤ K) →
      ∀ (c : V → ℂ), (∀ i, ‖c i‖ ≤ 1) →
      let D := ActualOriginalQPointSetup.pointDatum R J p (m+1) o
      ∀ (x : IndependentTests (ActualRunQlocalNativeTuple.orbit D)) (s : (Stock.census V).Mode)
      (U : Config G (R.family.side (m+1) p)),
      ‖ActualStartupNormalizedQ.modeObservable Q D u (μ-t) orders
        (FullQLocal.VariableScaling.tests c (testInclusion _ x)) s U‖ ≤ A*(1+‖t‖)^q := by
  obtain ⟨a,ha,q,hq⟩ := columns Q u R K μ
  refine ⟨a^(Fintype.card V),one_le_pow₀ ha,q*(Fintype.card V),?_⟩
  intro m p o t orders hk c hc
  dsimp only
  intro x s U
  let D := ActualOriginalQPointSetup.pointDatum R J p (m+1) o
  let T := a*(1+‖t‖)^q
  have ht : 1 ≤ T := one_le_mul_of_one_le_of_one_le ha (one_le_pow₀ (by linarith [norm_nonneg t]))
  refine (readout Q D u (μ-t) orders _ s U).trans ?_
  calc mode Q D u (μ-t) orders (FullQLocal.VariableScaling.tests c (testInclusion _ x)) s ≤ ∏ _ ∈ s.val,T := by
         apply Finset.prod_le_prod (fun i _ => mul_nonneg (norm_nonneg _) (column_nonneg Q (u i) _ _))
         intro i _
         have hr : ‖ActualRunQlocalNativeTuple.reader D i (FullQLocal.VariableScaling.tests c (testInclusion _ x) i)‖ ≤ 1 := by
           change ‖ActualRunQlocalNativeTuple.reader D i (c i • testInclusion _ x i)‖ ≤ 1
           rw [map_smul,norm_smul]
           simpa only [one_mul] using mul_le_mul (hc i) (reader R J p (m+1) o x i) (norm_nonneg _) zero_le_one
         simpa only [one_mul] using mul_le_mul hr (hq i (orders i) (hk i) t) (column_nonneg Q (u i) _ _) zero_le_one
       _ = T^s.val.card := by simp
       _ ≤ T^(Fintype.card V) := pow_le_pow_right₀ ht (Finset.card_le_univ _)
       _ = _ := by dsimp only [T]; rw [mul_pow,pow_mul]

end YM.Integration.WilsonPointStartupPrice
