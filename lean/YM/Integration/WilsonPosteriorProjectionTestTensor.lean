import YM.Integration.WilsonPosteriorProjectionTestGrowth
import YM.Integration.FVA1Physical.Round2.FormalFieldOrder
import YM.MSbar.MeasureP.Pins

/-! Contract the original spatial ledger against the whole, uncut prescribed
test curve. No supremum over the size of the torus is taken. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionTestTensor

open Set Function Filter Finset Lattice Wilson RG Source Labels Next.Foundations Precision Tree Exterior
open MSbar MSbar.Cacao MSbar.Whisk MSbar.Lis MSbar.CrossH Push.Uniform
open FVA1Physical.Round2.Curvature WilsonPosteriorProjectionTestGrowth
open scoped Classical Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

private theorem entry {σ : Type} [Fintype σ] [DecidableEq σ] {q : ℕ}
    {f : Positions σ → ℝ} {z : Positions σ} (hf : ContDiffAt ℝ q f z) (v : Fin q → σ) :
    iteratedFDeriv ℝ q f z (fun i => bolt (v i)) = buoy f z (List.ofFn v) := by
  have read (l : List σ) (length : l.length=q) :
      buoy f z l = iteratedFDeriv ℝ q f z (fun i => bolt (l.get (i.cast length.symm))) := by
    subst q
    exact CrossH.chain f l l.length z hf le_rfl
  simpa using (read (List.ofFn v) (by simp)).symm

private theorem distance {n : Side} (b : Site n) {q : ℕ} (v : Fin q → Primary n G) (i : Fin q) :
    separation (v i).1.1 b ≤ extent (zone (Measuring.chart n G) {b} (List.ofFn v)) := by
  apply Whisk.curve
  · apply Finset.mem_union_right
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨v i, List.mem_ofFn.mpr ⟨i,rfl⟩, rfl⟩
  · exact Finset.mem_union_left _ (Finset.mem_singleton_self b)

/-- This is precisely the `Yarn` expression defining the manuscript's
`fieldDistance`, evaluated at one common base point and at the full
prescribed derivatives of the test, with unequal partition sizes allowed. -/
theorem actual (H : Hol G) (d : ℕ) (J : Jet G) {q : ℕ} (orders : Fin q → ℕ) (s : ℕ)
    (reserve : ∑ i, (orders i-1) ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : Side) (b : Site n) (g θ a : ℝ),
      0 < g → 0 ≤ θ → θ ≤ 1 → 0 ≤ a →
      ∀ (f h : Positions (Primary n G) → ℝ), ContDiffAt ℝ q f 0 → ContDiffAt ℝ q h 0 →
      let test := fun i => iteratedDeriv (orders i) (WilsonPosteriorProjectionTestGrowth.curve H d b (θ • J) g) 0
      |iteratedFDeriv ℝ q f 0 test - iteratedFDeriv ℝ q h 0 test| ≤
        C*(g⁻¹*θ)^q * Yarn q (fun l =>
          |buoy f 0 l - buoy h 0 l| * spread (Measuring.chart n G) {b} a s l) := by
  choose K pos bill using fun i => WilsonPosteriorProjectionTestGrowth.spatial H d (orders i) J
  refine ⟨∏ i, K i,Finset.prod_pos (fun i _ => pos i),?_⟩
  intro n b g θ a hg hθ θ1 ha f h hf hh test
  let price := (∏ i, K i) * (g⁻¹*θ)^q
  have price0 : 0 ≤ price :=
    mul_nonneg (Finset.prod_nonneg fun i _ => (pos i).le) (pow_nonneg (mul_nonneg (inv_pos.mpr hg).le hθ) _)
  have toll (v : Fin q → Primary n G) :
      (∏ i, |test i (v i)|) ≤ price * spread (Measuring.chart n G) {b} a s (List.ofFn v) := by
    let L := extent (zone (Measuring.chart n G) {b} (List.ofFn v))
    let B := 1+(L:ℝ)
    have B1 : 1 ≤ B := le_add_of_nonneg_right (Nat.cast_nonneg L)
    have factor (i : Fin q) : |test i (v i)| ≤ ((g⁻¹*θ)*K i)*B^(orders i-1) := by
      have loc := distance b v i
      have bigger : 1+(separation (v i).1.1 b : ℝ) ≤ B :=
        add_le_add le_rfl (Nat.cast_le.mpr loc)
      calc
        _ ≤ g⁻¹*(K i*θ*(1+(separation (v i).1.1 b : ℝ))^(orders i-1)) := bill i n b g θ hg hθ θ1 (v i)
        _ = ((g⁻¹*θ)*K i)*(1+(separation (v i).1.1 b : ℝ))^(orders i-1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) bigger _)
          (mul_nonneg (mul_nonneg (inv_pos.mpr hg).le hθ) (pos i).le)
    have weight : B^s ≤ spread (Measuring.chart n G) {b} a s (List.ofFn v) :=
      le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans B1) _)
        (Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg L)))
    calc
      _ ≤ ∏ i, (((g⁻¹*θ)*K i)*B^(orders i-1)) := Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => factor i)
      _ = price * B^(∑ i, (orders i-1)) := by
        rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,Finset.prod_const,
          Finset.card_univ,Fintype.card_fin,Finset.prod_pow_eq_pow_sum]
        unfold price
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ((pow_le_pow_right₀ B1 reserve).trans weight) price0
  let T := iteratedFDeriv ℝ q f 0 - iteratedFDeriv ℝ q h 0
  have entries (v : Fin q → Primary n G) :
      T (fun i => bolt (v i)) = buoy f 0 (List.ofFn v) - buoy h 0 (List.ofFn v) := by
    simp only [T,_root_.sub_apply,entry hf v,entry hh v]
  let terms (i : Fin q) (u : Primary n G) := test i u • bolt u
  have expand : test = fun i => ∑ u,terms i u := funext fun i => spiral (test i)
  change |T test| ≤ price * _
  rw [expand,T.map_sum terms,word_function_sum,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro v _
  change |T (fun i => test i (v i) • bolt (v i))| ≤ _
  rw [T.map_smul_univ,smul_eq_mul,abs_mul,Finset.abs_prod,entries]
  exact (mul_le_mul_of_nonneg_right (toll v) (abs_nonneg _)).trans_eq (by ring)

end YM.Integration.WilsonPosteriorProjectionTestTensor
end

