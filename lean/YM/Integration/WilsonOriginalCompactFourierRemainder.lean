import YM.Integration.WilsonOriginalSignedTailSum

/-! Sum the signed, differentiated Fourier remainder on the entire physical
box, on one tail for every observation point (unit phase) of that box. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCompactFourierRemainder
open Filter Function Finset Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb
open scoped Topology BigOperators
open WilsonOriginalLowFourierJets (cube jet)
open WilsonOriginalSignedTailSum (high remainder)
open WilsonOriginalFourierLattice (height)
open WilsonOriginalTestedFourierBank (Prices)

theorem original {G : Gauge} {d j : ℕ} {warm : ℝ → ℝ} (hG : G.Simple) (paid : Coupling G warm)
    {read : ℝ → (Fin d → ℤ) → ℂ} {coeff : ℕ → (Fin d → ℤ) → ℂ}
    (b : Prices warm read coeff) (p : ℕ) (axis : Fin j → Fin d) (unit : Fin j → ℂ) :
    let Q := p+1+12*(d+j+b.loss)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r : ℝ in trail, ∀ phase : (Fin d → ℤ) → ℂ,
      (∀ v, ‖phase v‖ ≤ 1) → let u := warm r
      let field := fun v => phase v*jet axis unit v*remainder u Q (read r) coeff v
      Summable field ∧ ‖∑' v, field v‖ ≤ C*u^(p+1) := by
  intro Q
  obtain ⟨B,hB,large⟩ := WilsonOriginalSignedTailSum.original hG paid b Q (p+1) axis unit
  obtain ⟨A,hA,tests⟩ := b.tested Q
  let M := ∏ i, ‖unit i‖
  have hM : 0 ≤ M := prod_nonneg fun _ _ => norm_nonneg _
  let cost : ℝ := 3^d*2^b.loss*A*M
  have hc : 0 ≤ cost := by dsimp [cost];positivity
  refine ⟨cost+B,add_nonneg hc hB,?_⟩
  have cold := WilsonOriginalTemperatureDecay.original paid
  filter_upwards [large 1 zero_lt_one,tests,paid.positive,(tendsto_order.mp cold).2 1 zero_lt_one]
      with r income testsAt hu hu1 phase normPhase u field
  let N := ⌊(u⁻¹)^12⌋₊
  let bank := cube d N
  let small := fun v => if v ∈ bank then field v else 0
  let rem := remainder u Q (read r) coeff
  let far := high u axis unit phase rem
  have low (v) (hv : v ∈ bank) : ‖rem v‖ ≤ A*u^Q*(1+(N:ℝ))^b.loss := by
    have below := (WilsonOriginalIntegerModeCut.member v N).mp hv
    have k : (height v:ℝ) ≤ N := by exact_mod_cast below
    have h := testsAt v
    rw [WilsonOriginalIntegerModeCut.size_pow] at h
    exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _) (by positivity))
  have compact := WilsonOriginalLowFourierJets.original (d:=d) (j:=j) (p:=p+1) (loss:=b.loss)
    (Q:=Q) (by rfl) axis unit u A hu hu1.le hA phase rem normPhase low
  have smallBill : ‖∑' v, small v‖ ≤ cost*u^(p+1) := by
    have eqv : ∑' v, small v = ∑ v ∈ bank,field v := calc
      _ = ∑ v ∈ bank, small v := tsum_eq_sum (fun v hv => by simp [small,hv])
      _ = _ := sum_congr rfl fun v hv => by simp [small,hv]
    rw [eqv]
    exact compact
  have hs : Summable small := summable_of_ne_finset_zero (s:=bank) fun v hv => by simp [small,hv]
  obtain ⟨ht,price⟩ := income phase normPhase
  have hfar : Summable far := ht.of_norm
  have join : field = fun v => small v + far v := by
    funext v
    by_cases hv : v ∈ bank
    · have yes : v ∈ cube d ⌊(u⁻¹)^12⌋₊ := hv
      simp only [small,far,high,if_pos hv,if_pos yes,add_zero]
    · have no : v ∉ cube d ⌊(u⁻¹)^12⌋₊ := hv
      simp only [small,far,high,if_neg hv,if_neg no,zero_add]
      rfl
  have convergence : Summable field := by rw [join];exact hs.add hfar
  refine ⟨convergence,?_⟩
  rw [join,hs.tsum_add hfar]
  have rest : ‖∑' v, far v‖ ≤ B*u^(p+1) :=
    (norm_tsum_le_tsum_norm ht).trans (by simpa [far,rem,u] using price)
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ cost*u^(p+1)+B*u^(p+1) := add_le_add smallBill rest
    _ = _ := (add_mul _ _ _).symm

end YM.Integration.WilsonOriginalCompactFourierRemainder

