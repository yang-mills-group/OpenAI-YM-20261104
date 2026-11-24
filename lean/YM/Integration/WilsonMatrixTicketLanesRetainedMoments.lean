import YM.FVA2.OrbitWick

/-! The actual Markov conditional Gaussian with its retained affine displacement in every Wick term. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRetainedMoments
open Function Filter MeasureTheory Finset Lattice Gauge FVA2 FVA2.Wick PertExtension.GaussianScore
open Next.Rank Next.Rank.Normal
open scoped Topology BigOperators Classical
variable {E H V : Type*} [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (Γ : Law E) (L : H → Module.Dual ℝ E) (μ : Measure E) [μ.IsAddHaarMeasure]
  (f : V→H) (s : Finset V) (a : E)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A row is expanded before summing over the submitted signed polynomial terms. -/
theorem expand (y : E) : Law.product (L ∘ f) s (y+a) =
    ∑t∈s.powerset,(∏v∈s\t,L (f v) a)*Law.product (L ∘ f) t y := by
  simp only [Law.product,comp_apply,map_add]
  simpa only [mul_comm] using (Finset.prod_add (fun v=>L (f v) y) (fun v=>L (f v) a) s)

/-- A retained factor is the actual mean of that same gauge leg, and every remaining selected
leg is contracted with the actual finite inverse Hessian. The empty block is included. -/
theorem shifted : Γ.average μ (fun y=>Law.product (L ∘ f) s (y+a)) =
  ∑ t∈s.powerset,(∏v∈s\t,L (f v) a)*(blend (color Γ L) 0 (glyphs f t)).re := by
  let fee (t : Finset V):=∏v∈s\t,L (f v) a
  let Q (t : Finset V) := Law.product (L ∘ f) t
  have purchase (t : Finset V) : Integrable (fun y=>Q t y*Γ.kern y) μ :=
    Γ.integrable_entry μ (Law.product_bound (L ∘ f) t) (Law.product_cont (L ∘ f) t)
  have correct (t : Finset V) : Γ.average μ (Q t)=(blend (color Γ L) 0 (glyphs f t)).re :=
    congrArg Complex.re (monomial_wick Γ L μ f t)
  change (∫ y, Law.product (L ∘ f) s (y+a)*Γ.kern y ∂μ)/(∫ y,Γ.kern y ∂μ)=_
  simp_rw [expand L f s a,Finset.sum_mul,mul_assoc]
  rw [integral_finsetSum _ (fun t _=>(purchase t).const_mul (fee t)),Finset.sum_div]
  apply Finset.sum_congr rfl;intro t _;rw [integral_const_mul,mul_div_assoc,←correct];rfl

/-- The finite recorded stencil can carry signed coefficients and genuine repeated occurrences. -/
theorem total {M : Type*} (m : Finset M) (terms : M→Finset V) (c : M→ℝ) (a : E) :
    Γ.average μ (fun y=>∑j∈m,c j*Law.product (L ∘ f) (terms j) (y+a)) =
    ∑j∈m,c j* ∑ t∈(terms j).powerset,(∏v∈(terms j)\t,L (f v) a)*(blend (color Γ L) 0 (glyphs f t)).re := by
  have source (j : M) : Integrable (fun y=>Law.product (L ∘ f) (terms j) (y+a)*Γ.kern y) μ := by
    simp_rw [expand L f (terms j) a,Finset.sum_mul,mul_assoc]
    refine integrable_finsetSum _ (fun t _=>?_)
    exact (Γ.integrable_entry μ (Law.product_bound (L ∘ f) t) (Law.product_cont (L ∘ f) t)).const_mul _
  change (∫ y,(∑j∈m,c j*Law.product (L ∘ f) (terms j) (y+a))*Γ.kern y ∂μ)/(∫ y,Γ.kern y ∂μ)=_
  simp_rw [Finset.sum_mul,mul_assoc]
  rw [integral_finsetSum _ (fun j _=>(source j).const_mul (c j)),Finset.sum_div]
  apply Finset.sum_congr rfl;intro j _;rw [integral_const_mul,mul_div_assoc,←shifted Γ L μ f (terms j) a];rfl

end YM.Integration.WilsonMatrixTicketLanesRetainedMoments
