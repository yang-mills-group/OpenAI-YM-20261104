import YM.FormalOPE.RG10.Routes.Magnitude

/-! # The actual cost of substitute with rooted polynomial tickets

Use e.g. genuine linear stationary predictor `A_tr B` plus `id ξ` at the declared joint law and
same formal coupling variable `g`. Use after encoding adjacent-coupling ratio corrections on B.
Pulling all port budgets individually (not same moment estimate, but FINITE cost per join,
using higher finite moments on the inputs). Norm bounds on the rooted shift rows must be supplied.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Route
open Function Finset MvPolynomial PowerSeries Bulk
open scoped Topology BigOperators Classical
variable {I B X : Type} {T : Tape X}
    (p : I→ X) (q : B→ X)
    (w : I→Channel B)
    (A : Lens T)
    (n r : ℕ) (C : ℝ) (h : 1 ≤ C)
local notation "ν" => A.m ∘ p
local notation "μ" => A.m ∘ q

-- producer pays each shift coefficient separately when compiling its row

def stencilCost (T : Tape X) := ∀ i, mag (fun a=> T.Δ (p i) (q a)) n r (w i) ≤ C
variable (hw : stencilCost p q w n r C T)
include hw

lemma march_pin (i : I) : mag μ n r (w i) ≤ tip (A.m (p i)) n*C := (ride μ n r (fun _=>A.sign _) _ (A.sign _)
  (fun j => A.path (q j) (p i)) (fun _=> T.sign ..)).trans (mul_le_mul_of_nonneg_left (hw i) (tip_pos (A.sign _) n).le)
variable (m : Letters I)
include h
private lemma march_verse (d : ℕ) (c : ℂ) (hm : Primitives.GCC.LocalPolynomial.length m ≤ d) :
    mag μ n r (MvPolynomial.aeval w (MvPolynomial.monomial m c : Packet I)) ≤ C^d*(fare ν (n*d) m * ‖c‖) := by
  let V := fare ν n m; have h0 : 0 ≤ μ := fun j => A.sign (q j); have hu : 1 ≤ V:=fare_one _ (fun j=> A.sign (p j)) _ _
  have h1 : 0≤C := zero_le_one.trans h
  have hZ := zero_le_one.trans hu
  rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,one_mul, mag_smul]
  apply le_trans (b:=‖c‖*(V*C)^d) (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) ?_
  · unfold Finsupp.prod; apply (mag_prod μ n r h0 _ _).trans
    apply le_trans (prod_le_prod (fun j _ => mag_sign μ n r h0 (w j ^ m j)) (fun j hj => (mag_pow μ n r h0 _ _).trans (pow_le_pow_left₀ (mag_sign _ _ _ h0 _) ((march_pin p q w A n r C hw j).trans (mul_le_mul_of_nonneg_right (tip_mono (show A.m (p j) ≤ along ν m.support from le_along hj (A.m ∘ p)) (A.sign _) _) h1)) (m j)))) _
    rw [prod_pow_eq_pow_sum]; exact pow_le_pow_right₀ (hu.trans (le_mul_of_one_le_right hZ h)) hm
  apply le_of_eq; rw [mul_pow, show fare ν (n*d) m=V^d from pow_mul ..]; ring

private lemma marching_body (i : Packet I) (d : ℕ) (hd : MvPolynomial.totalDegree i ≤ d) :
    mag μ n r (MvPolynomial.aeval w i) ≤ C^d*worth ν (n*d) i := by
  nth_rw 1 [i.as_sum]; rw [map_sum,worth,Finset.mul_sum]; apply (mag_sum μ n r (fun _=>A.sign _) _ _).trans;
  exact sum_le_sum fun _ hx => march_verse p q w A n r C h hw _ d _ ((MvPolynomial.le_totalDegree hx).trans hd)

theorem transported (P : Channel I) (d : ℕ) (hd : Binary.slim P r d) :
    mag μ n r (replot w P) ≤ C^d * mag ν (n*d) r P := by
  let X (x : ℕ×ℕ) := worth μ n (PowerSeries.coeff x.2 (MvPolynomial.aeval w (PowerSeries.coeff x.1 P)))
  refine le_trans (b:=∑ i∈ range (r+1),∑ j∈antidiagonal i,X j) (sum_le_sum fun i hi => ?_)
    (le_trans (triangle_le r X (fun (x:ℕ×ℕ)=> show 0 ≤ X x from worth_nonneg μ (fun i=>A.sign (q i)) n (PowerSeries.coeff x.2 (MvPolynomial.aeval w (PowerSeries.coeff x.1 P))))) ?_)
  · rw [replot_coeff]; exact worth_sum _ (fun _=>A.sign _) _ _ _
  rw [mag,Finset.mul_sum]; apply sum_le_sum; intro i hi; have hn : i ≤ r:= Nat.le_of_lt_succ (mem_range.mp hi)
  change mag μ n r (MvPolynomial.aeval w (PowerSeries.coeff i P)) ≤ _
  exact marching_body p q w A n r C h hw (PowerSeries.coeff i P) d (hd i hn)
end YM.FormalOPE.RG10.Route
