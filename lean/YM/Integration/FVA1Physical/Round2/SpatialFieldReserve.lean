import YM.Integration.FVA1Physical.Round2.RootedInterpolation
import YM.MSbar.Heath.Rad

/-! Interpolate on the actual torus with one root and all ordered derivative
addresses. The price for the lost spatial exponent is independent of the
period; each further address pays one copy of a summable radial kernel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Lattice Finset MSbar.Whisk MSbar.Heath
open scoped Classical BigOperators
variable {σ : Type} [Fintype σ] {n : Side}

omit [Fintype σ] in
private theorem word_factor (site : σ → Site n) (b : Site n) {a : ℝ} (ha : 0 ≤ a)
    (l : List σ) (d : ℕ) (inside : ∀ i ∈ l, separation b (site i) ≤ d) :
    (Real.exp (-a*d)) ^ l.length ≤
      (l.map fun i => Real.exp (-a*separation b (site i))).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.length_cons,pow_succ',List.map_cons,List.prod_cons]
    apply mul_le_mul _ (ih fun j hj => inside j (List.mem_cons_of_mem _ hj))
      (pow_nonneg (Real.exp_pos _).le _) (Real.exp_pos _).le
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
      (Nat.cast_le.mpr (inside i List.mem_cons_self)) (neg_nonpos.mpr ha))

theorem spatial_weight_trade (site : σ → Site n) (b : Site n) (a : ℝ) (ha : 0 ≤ a)
    (s : ℕ) (l : List σ) :
    spread site {b} a s l ^ 2 ≤
      spread site {b} (((l.length:ℝ)+2)*a) (s+s) l *
      (l.map fun i => Real.exp (-a*separation b (site i))).prod := by
  let d:=extent (zone site {b} l)
  have h:=word_factor site b ha l d fun i hi => curve
    (Finset.mem_union_left _ (Finset.mem_singleton_self b))
    (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨i,hi,rfl⟩)))
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left h (effect site _ _ _ _).le)
  change ((1+(d:ℝ))^s * Real.exp (a*d))^2 =
    (1+(d:ℝ))^(s+s) * Real.exp ((((l.length:ℝ)+2)*a)*d) * (Real.exp (-a*d))^l.length
  rw [mul_pow,pow_add,← Real.exp_nat_mul,← Real.exp_nat_mul,mul_assoc,← Real.exp_add]
  congr 1
  · ring
  congr 1
  push_cast
  ring

/-- Only the number of coordinates over a site enters the cost; the period
may be chosen after all constants. The sharper exponent is spent once. -/
theorem spatial_field_trade (site : σ → Site n) (b : Site n) {a ε M D τ : ℝ}
    (ha : 0 ≤ a) (hε : 0 ≤ ε) (hτ : 0 < τ) (q s : ℕ) (err : List σ → ℝ)
    (small : ∀ l, l.length=q → 0 ≤ err l ∧ err l ≤ ε)
    (bank : Yarn q (fun l=>err l * spread site {b} (((q:ℝ)+2)*a) (s+s) l) ≤ M)
    (kernel : (∑ i,Real.exp (-a*separation b (site i))) ≤ D) :
    Yarn q (fun l=>err l * spread site {b} a s l) ≤ τ*M+(ε/τ)*D^q := by
  let cost (i : σ):=Real.exp (-a*separation b (site i))
  refine rooted_word_trade q err (spread site {b} a s)
    (spread site {b} (((q:ℝ)+2)*a) (s+s)) (fun l=>(l.map cost).prod)
    hτ hε ?_ bank ?_
  · intro l hl
    refine ⟨(small l hl).1,(small l hl).2,effect ..,(effect ..).le,?_,?_⟩
    · exact List.prod_nonneg fun x hx => by
        obtain ⟨i,_,rfl⟩:=List.mem_map.mp hx
        exact (Real.exp_pos _).le
    simpa only [hl] using spatial_weight_trade site b a ha s l
  rw [product_word_cost]
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) kernel _

theorem spatial_site_price {a : ℝ} (ha : 0 < a) (b : Site n) :
    (∑ i:Site n,Real.exp (-a*separation b i)) ≤ 81*meter a := radial a ha b

end YM.Integration.FVA1Physical.Round2.Curvature
