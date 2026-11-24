import YM.Integration.WilsonPhysicalExteriorFormalGram

/-! Quantitative price of the complete independently booked MS far detector, including
every positive coupling coefficient and the full matrix of lower and mixed grades. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorFormalPrice
open Function Matrix Pert Pert.Position MS MS.Land MS.Menus MS.Logarithm FVA2 Extra.FD
open WilsonPhysicalExteriorFormalGram
open scoped Classical BigOperators
variable {G : Gauge} {B : MS.Local.Physical.Deck G} {A : Booked B}
variable (V : Warehouse G) (M : MS_Data G A) (h : ℕ) (p q : E4)
local notation "I" => Glyph B h
local notation "𝒦" => Matrix I I ℂ

private def polynomial (X : ℝ → 𝒦) : Prop := ∀ a b, Ready (fun u => X u a b)

private theorem fixed (D : 𝒦) : polynomial h (fun _ => D) := fun a b => Ready.const (D a b)

private theorem times {X Y : ℝ → 𝒦} (hX : polynomial h X) (hY : polynomial h Y) :
    polynomial h (fun u => X u * Y u) := by
  intro a b
  change Ready (fun u => ∑ i, X u a i * Y u i b)
  have hh := Ready.sums Finset.univ (k:=fun i u => X u a i * Y u i b)
    (fun i _ => Ready.pair (LinearMap.mul ℝ ℂ) (hX a i) (hY i b))
  convert hh using 1
  funext u
  simp only [Finset.sum_apply]

private theorem sum {L : Type} (l : Finset L) {X : L → ℝ → 𝒦}
    (hX : ∀ j∈l, polynomial h (X j)) : polynomial h (fun u => ∑ j∈l, X j u) := by
  intro a b
  have hh := Ready.sums l (k:=fun j u => X j u a b) (fun j hj => hX j hj a b)
  convert hh using 1
  funext u
  simp only [Matrix.sum_apply,Finset.sum_apply]

private theorem original (hp : p≠q) (k : ℕ) :
    polynomial h (fun u => PowerSeries.coeff k (matrix M h p q u)) := by
  intro a b
  let z := Fountain.metric (couple p q)
  have hs := MSExteriorFiniteScales.tour_polynomial M (word h a b)
    (fun _ : Unit => z) (fun _ => Fountain.metric_conf (couple_ok hp)) k
  have r := hs.linear (LinearMap.proj (R:=ℝ) (φ:=fun _ : Unit => ℂ) ())
  change Ready (fun u => MSExteriorDilation.moment M (word h a b) u z k) at r
  simp only [matrix,PowerSeries.coeff_mk]
  exact r

/-- The actual inverse coefficient, including all lower perturbative orders of the
original named Gram, is a polynomial in the subtraction logarithm. -/
theorem inverse_polynomial (hp : p≠q) (k : ℕ) : ∀ a b : I, Ready
    (fun u => PowerSeries.coeff k (inverse V M h p q hp u) a b) := by
  change polynomial h (fun u => PowerSeries.coeff k (inverse V M h p q hp u))
  induction k using Nat.strong_induction_on with
  | h k ih =>
    let U := tree V M h p q hp
    by_cases hk : k=0
    · subst k
      have eq : (fun u => PowerSeries.coeff 0 (inverse V M h p q hp u)) =
          (fun _ : ℝ => (↑U⁻¹ : 𝒦)) := by
        funext u
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,inverse,PowerSeries.constantCoeff_invOfUnit]
      rw [eq]
      exact fixed h _
    · let X (ab : ℕ×ℕ) (u : ℝ) : 𝒦 := if ab.2<k then
          PowerSeries.coeff ab.1 (matrix M h p q u) * PowerSeries.coeff ab.2 (inverse V M h p q hp u)
        else 0
      have hX (ab : ℕ×ℕ) : polynomial h (X ab) := by
        by_cases ht : ab.2<k
        · simpa only [X,if_pos ht] using
            (times h (original M h p q hp ab.1) (ih ab.2 ht))
        · simpa only [X,if_neg ht] using (fixed h (0:𝒦))
      have full := times h (fixed h (-↑U⁻¹ : 𝒦))
        (sum h (Finset.HasAntidiagonal.antidiagonal k) (X:=X) (fun ab _ => hX ab))
      have eq : (fun u => PowerSeries.coeff k (inverse V M h p q hp u)) =
          (fun u => (-↑U⁻¹ : 𝒦) * ∑ ab∈Finset.HasAntidiagonal.antidiagonal k, X ab u) := by
        funext u
        change PowerSeries.coeff k ((matrix M h p q u).invOfUnit (tree V M h p q hp)) = _
        rw [PowerSeries.coeff_invOfUnit,if_neg hk]
        rfl
      rw [eq]
      exact full

private theorem bound {f : ℝ → ℂ} (hf : Ready f) :
    ∃ A : ℝ, 0≤A ∧ ∃ d : ℕ, ∀ u : ℝ, ‖f u‖ ≤ A*(1+|u|)^d := by
  let L : ℂ →ₗ[ℝ] (Unit→ℂ) := LinearMap.pi (fun _ => LinearMap.id)
  have fid : Ready (fun u (_:Unit) => f u) := hf.linear L
  obtain ⟨N,A,hA,d,he⟩ := MSExteriorFiniteScales.finite_observations fid
  let C := ∑ k∈Finset.range N, ‖f k‖
  have hC : 0≤C := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hn (k : ℕ) (hk : k∈Finset.range N) : ‖f k‖ ≤ C :=
    Finset.single_le_sum (f:=fun j : ℕ => ‖f (j:ℝ)‖) (fun _ _ => norm_nonneg _) hk
  refine ⟨A*C,mul_nonneg hA hC,d,fun u => ?_⟩
  exact (he () u C hC hn).trans_eq (by ring)

private theorem finite_bank (hp : p≠q) (N : ℕ) :
    ∃ A : ℝ, 0≤A ∧ ∃ d : ℕ, ∀ k≤N, ∀ a b : I, ∀ u : ℝ,
      ‖PowerSeries.coeff k (inverse V M h p q hp u) a b‖ ≤ A*(1+|u|)^d := by
  let Index := Fin (N+1) × I × I
  have hh (i : Index) := bound (inverse_polynomial V M h p q hp i.1 i.2.1 i.2.2)
  choose c hc d hd using hh
  let K := ∑ i, c i
  let D := ∑ i, d i
  refine ⟨K,Finset.sum_nonneg (fun i _ => hc i),D,?_⟩
  intro k hk a b u
  let i : Index := (⟨k,by omega⟩,a,b)
  have hK : c i≤K := Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i)
  have hD : d i≤D := Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)
  exact (hd i u).trans (mul_le_mul hK (pow_le_pow_right₀ (by linarith only [abs_nonneg u]) hD)
    (pow_nonneg (by positivity) _) ((hc i).trans hK))

/-- One price before the far distance, the two independent original field slots,
and all coupling coefficients through N. The engineering power is h, with only
a polynomial in log T in addition. -/
theorem sharp (hp : p≠q) (μ : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∃ d : ℕ, ∀ T : ℝ, 1≤T → ∀ k≤N, ∀ a b : I,
      ‖PowerSeries.coeff k (decoder V M h p q hp μ (Real.log T)) a b‖ ≤
        C*T^h*(1+Real.log T)^d := by
  obtain ⟨K,hK,d,hd⟩ := finite_bank V M h p q hp N
  refine ⟨K*(1+|μ|)^d,mul_nonneg hK (by positivity),d,?_⟩
  intro T hT k hk a b
  have hl := Real.log_nonneg hT
  have hT₀ := lt_of_lt_of_le zero_lt_one hT
  have hb : b.size≤h := by change b.1.val≤h; have := b.1.isLt; omega
  have charge_bound : ‖charge h (Real.log T) b‖ ≤ T^h := by
    rw [charge,MSExteriorDilation.power,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
      Real.exp_nat_mul,Real.exp_log hT₀]
    exact pow_le_pow_right₀ hT hb
  have hp₀ : 1+|μ+Real.log T| ≤ (1+|μ|)*(1+Real.log T) := by
    have lo := abs_add_le μ (Real.log T)
    rw [abs_of_nonneg hl] at lo
    nlinarith only [lo,mul_nonneg (abs_nonneg μ) hl]
  rw [decoder,PowerSeries.coeff_mul_C,gear,Matrix.mul_diagonal,norm_mul]
  calc
    _ ≤ (K*(1+|μ+Real.log T|)^d)*T^h :=
      mul_le_mul (hd k hk a b _) charge_bound (norm_nonneg _) (by positivity)
    _ ≤ (K*((1+|μ|)*(1+Real.log T))^d)*T^h := by gcongr
    _ = _ := by rw [mul_pow]; ring

/-- Price of reconstruction of an arbitrary signed far row in the actual physical
horizon, in the finite sup norm, without an engineering loss at positive order. -/
theorem readout (hp : p≠q) (μ : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∃ d : ℕ, ∀ T : ℝ, 1≤T → ∀ k≤N, ∀ y : I → ℂ,
      ‖(PowerSeries.coeff k (decoder V M h p q hp μ (Real.log T))).vecMul y‖ ≤
        C*T^h*(1+Real.log T)^d*‖y‖ := by
  obtain ⟨K,hK,d,hd⟩ := sharp V M h p q hp μ N
  refine ⟨(Fintype.card I:ℝ)*K,mul_nonneg (Nat.cast_nonneg _) hK,d,?_⟩
  intro T hT k hk y
  have hl := Real.log_nonneg hT
  have hT₀ := zero_le_one.trans hT
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro b
  let A := PowerSeries.coeff k (decoder V M h p q hp μ (Real.log T))
  change ‖∑ a, y a*A a b‖ ≤ _
  calc
    _ ≤ ∑ a, ‖y a*A a b‖ := norm_sum_le ..
    _ ≤ ∑ _a : I, ‖y‖*(K*T^h*(1+Real.log T)^d) := Finset.sum_le_sum fun a _ => by
      rw [norm_mul]
      exact mul_le_mul (norm_le_pi_norm y a) (hd T hT k hk a b) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end YM.Integration.WilsonPhysicalExteriorFormalPrice
end
