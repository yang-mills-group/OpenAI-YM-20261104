import YM.Integration.WilsonPhysicalExteriorSmoothGram

/-! The sharp inverse price for the actual compact smooth MS detector, at all
coupling orders through the chosen order. The test can be fixed before that
order or the subtraction point, in any prescribed separated neighborhood. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorSmoothPrice
open Set Filter Function Polynomial Matrix Pert Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone
open FVA2 FVA2.ColorCode Extra.FD
open WilsonPhysicalExteriorFormalGram (charge gear)
open WilsonPhysicalExteriorSmoothGram
open scoped Classical BigOperators Topology

variable {G:Gauge} {B:MS.Local.Physical.Deck G}{A:Booked B}
variable (M:MS_Data G A)(h:ℕ)(g:Test 2)
local notation "I" => Glyph B h

private def cash (P:Polynomial ℂ) := ∑ i ∈ Finset.range (P.natDegree+1), ‖P.coeff i‖
private theorem cash_nonnegative (P:Polynomial ℂ) : 0≤cash P :=
  Finset.sum_nonneg fun _ _=>norm_nonneg _

private theorem cash_eval (P:Polynomial ℂ) (u:ℝ) :
    ‖P.eval (u:ℂ)‖≤cash P*(1+|u|)^P.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  calc
    _ ≤ ∑ i ∈ Finset.range (P.natDegree+1), ‖P.coeff i*(u:ℂ)^i‖ := norm_sum_le ..
    _ ≤ ∑ i ∈ Finset.range (P.natDegree+1), ‖P.coeff i‖*(1+|u|)^P.natDegree :=
      Finset.sum_le_sum fun i hi=>by
        rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        have hd:i≤P.natDegree:=Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        exact (pow_le_pow_left₀ (abs_nonneg u) (show |u|≤1+|u| by linarith) i).trans
          (pow_le_pow_right₀ (by linarith only [abs_nonneg u]) hd)
    _ = _ := (Finset.sum_mul ..).symm

private theorem bank (hg:IsUnit (MSSeparatedTestGram.matrix M h 0 0 g)) (N:ℕ) :
    ∃ K:ℝ,0≤K ∧ ∃ d:ℕ,∀ k≤N,∀ a b:I,∀u:ℝ,
      ‖PowerSeries.coeff k (evaluatedInverse M h g hg u) a b‖ ≤ K*(1+|u|)^d := by
  let Idx:=Fin (N+1) × I × I
  let P(i:Idx) := PowerSeries.coeff i.1 (inverseP M h g hg) i.2.1 i.2.2
  let K:=∑ i:Idx, cash (P i)
  let d:=∑ i:Idx, (P i).natDegree
  refine ⟨K,Finset.sum_nonneg (fun i _=>cash_nonnegative (P i)),d,?_⟩
  intro k hk a b u
  let i:Idx:=(⟨k,by omega⟩,a,b)
  have hc:cash (P i)≤K:=Finset.single_le_sum (fun j _=>cash_nonnegative (P j)) (Finset.mem_univ i)
  have hd:(P i).natDegree≤d:=Finset.single_le_sum (fun j _=>Nat.zero_le (P j).natDegree) (Finset.mem_univ i)
  rw [evaluatedInverse,PowerSeries.coeff_map]
  change ‖(P i).eval (u:ℂ)‖≤K*(1+|u|)^d
  exact (cash_eval (P i) u).trans (mul_le_mul hc
    (pow_le_pow_right₀ (by linarith only [abs_nonneg u]) hd) (by positivity) ((cash_nonnegative _).trans hc))

theorem sharp (hg:IsUnit (MSSeparatedTestGram.matrix M h 0 0 g)) (μ:ℝ) (N:ℕ) :
    ∃ C:ℝ,0≤C ∧ ∃ d:ℕ,∀ T:ℝ,1≤T → ∀ k≤N,∀a b:I,
      ‖PowerSeries.coeff k (decoder M h g hg μ (Real.log T)) a b‖≤C*T^h*(1+Real.log T)^d := by
  obtain ⟨K,hK,d,hd⟩:=bank M h g hg N
  refine ⟨K*(1+|μ|)^d,mul_nonneg hK (by positivity),d,?_⟩
  intro T hT k hk a b
  have hl:=Real.log_nonneg hT
  have hT₀:=lt_of_lt_of_le zero_lt_one hT
  have hb:b.size≤h:=by change b.1.val≤h;have := b.1.isLt;omega
  have charge_bound:‖charge h (Real.log T) b‖≤T^h := by
    rw [charge,MSExteriorDilation.power,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
      Real.exp_nat_mul,Real.exp_log hT₀]
    exact pow_le_pow_right₀ hT hb
  have hp:=MSExteriorFiniteScales.running_log μ (Real.log T) hl
  rw [decoder,PowerSeries.coeff_mul_C,gear,Matrix.mul_diagonal,norm_mul]
  calc
    _ ≤ (K*(1+|μ+Real.log T|)^d)*T^h := mul_le_mul (hd k hk a b _) charge_bound (norm_nonneg _) (by positivity)
    _ ≤ (K*((1+|μ|)*(1+Real.log T))^d)*T^h := by gcongr
    _ = _ := by rw [mul_pow];ring

theorem readout (hg:IsUnit (MSSeparatedTestGram.matrix M h 0 0 g)) (μ:ℝ) (N:ℕ) :
    ∃ C:ℝ,0≤C ∧ ∃ d:ℕ,∀ T:ℝ,1≤T → ∀ k≤N,∀y:I→ℂ,
      ‖(PowerSeries.coeff k (decoder M h g hg μ (Real.log T))).vecMul y‖≤C*T^h*(1+Real.log T)^d*‖y‖ := by
  obtain ⟨K,hK,d,hd⟩:=sharp M h g hg μ N
  refine ⟨(Fintype.card I:ℝ)*K,mul_nonneg (Nat.cast_nonneg _) hK,d,?_⟩
  intro T hT k hk y
  have hl:=Real.log_nonneg hT
  have hT₀:=zero_le_one.trans hT
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro b
  let X:=PowerSeries.coeff k (decoder M h g hg μ (Real.log T))
  change ‖∑ a,y a*X a b‖≤_
  calc
    _≤∑ a,‖y a*X a b‖:=norm_sum_le ..
    _≤∑ _a:I,‖y‖*(K*T^h*(1+Real.log T)^d):=Finset.sum_le_sum fun a _=>by
      rw [norm_mul]; exact mul_le_mul (norm_le_pi_norm y a) (hd T hT k hk a b) (norm_nonneg _) (norm_nonneg _)
    _=_:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring

theorem purchased (V:Warehouse G) {p:E4} (hp:(0:E4)≠p) (U:Set (Points 2)) (hu:U∈𝓝 (couple 0 p)) :
    ∃ g:Test 2,tsupport g⊆U ∧ (∀z,(g z).im=0 ∧ 0≤(g z).re) ∧
      0<(g (couple 0 p)).re ∧ (∫ z,g z)=1 ∧
      ∃ hg:IsUnit (MSSeparatedTestGram.matrix M h 0 0 g),
      (∀μ s, far M h g μ s*decoder M h g hg μ s=1 ∧ decoder M h g hg μ s*far M h g μ s=1) ∧
      ∀μ:ℝ,∀ N:ℕ,∃ C:ℝ,0≤C ∧ ∃ d:ℕ,∀ T:ℝ,1≤T → ∀ k≤N,∀y:I→ℂ,
        ‖(PowerSeries.coeff k (decoder M h g hg μ (Real.log T))).vecMul y‖≤C*T^h*(1+Real.log T)^d*‖y‖ := by
  obtain ⟨g,scope,pos,seen,integral,good⟩:=MSSeparatedTestGram.localized V M h 0 hp U hu
  exact ⟨g,scope,pos,seen,integral,good,corrected V M h g good,readout M h g good⟩

end YM.Integration.WilsonPhysicalExteriorSmoothPrice
end
