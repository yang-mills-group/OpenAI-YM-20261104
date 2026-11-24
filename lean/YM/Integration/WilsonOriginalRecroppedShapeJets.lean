import YM.Integration.WilsonOriginalCompactFourierRemainder
import YM.Integration.WilsonOriginalSummableHeatJets

/-! Return from the accuracy needed for the spatial frequency split to
the publicly requested crop, on the same fixed field and physical clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalRecroppedShapeJets
open Filter Function Finset Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb
open scoped Topology BigOperators
open WilsonOriginalTestedFourierBank (Prices)
open WilsonOriginalLowFourierJets (jet)
open WilsonOriginalSignedTailSum (remainder)
variable {d j : ℕ}
private def field (read : ℝ → (Fin d → ℤ) → ℂ) (coeff : ℕ → (Fin d → ℤ) → ℂ)
    (axis : Fin j → Fin d) (unit : Fin j → ℂ) (warm : ℝ → ℝ) (q : ℕ) (r : ℝ)
    (phase : (Fin d → ℤ) → ℂ) (v : Fin d → ℤ) : ℂ :=
  phase v*jet axis unit v*remainder (warm r) q (read r) coeff v

private def Price (read : ℝ → (Fin d → ℤ) → ℂ) (coeff : ℕ → (Fin d → ℤ) → ℂ)
    (axis : Fin j → Fin d) (unit : Fin j → ℂ) (warm : ℝ → ℝ) (p q : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r : ℝ in trail, ∀ phase : (Fin d → ℤ) → ℂ,
    (∀ v, ‖phase v‖ ≤ 1) → let f := field read coeff axis unit warm q r phase
    Summable f ∧ ‖∑' v, f v‖ ≤ C*warm r^(p+1)

private theorem withdraw {G : Gauge} {warm : ℝ → ℝ} (hG : G.Simple) (paid : Coupling G warm)
    {read : ℝ → (Fin d → ℤ) → ℂ} {coeff : ℕ → (Fin d → ℤ) → ℂ}
    (b : Prices warm read coeff) (axis : Fin j → Fin d) (unit : Fin j → ℂ)
    {p e : ℕ} (pe : p ≤ e) (higher : Price read coeff axis unit warm p (e+1)) :
    Price read coeff axis unit warm p e := by
  obtain ⟨C,hC,cast⟩ := higher
  let posted := fun v => jet axis unit v*coeff (e+1) v
  let M := ∑' v, ‖posted v‖
  have hM : 0 ≤ M := tsum_nonneg fun _ => norm_nonneg _
  have absolute : Summable fun v => ‖posted v‖ := WilsonOriginalSummableHeatJets.original hG paid b (e+1) axis unit
  have cold := WilsonOriginalTemperatureDecay.original paid
  refine ⟨C+M,add_nonneg hC hM,?_⟩
  filter_upwards [paid.positive,(tendsto_order.mp cold).2 1 zero_lt_one,cast]
    with r hu hu1 del phase normPhase f
  let u := warm r
  let g := field read coeff axis unit warm (e+1) r phase
  let cut := fun v => (u:ℂ)^(e+1)*(phase v*posted v)
  have each (v) : ‖cut v‖ ≤ u^(e+1)*‖posted v‖ := by
    have hu' : 0 < u := hu
    simp only [cut,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu']
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg (posted v)) (normPhase v))
      (pow_nonneg hu'.le _)
  have total := absolute.mul_left (u^(e+1))
  have series := Summable.of_nonneg_of_le (fun v => norm_nonneg (cut v)) each total
  have cost : ‖∑' v,cut v‖ ≤ M * u^(p+1) := calc
    _ ≤ ∑' v, ‖cut v‖ := norm_tsum_le_tsum_norm series
    _ ≤ ∑' v,u^(e+1)*‖posted v‖ := series.tsum_le_tsum each total
    _ = M*u^(e+1) := by rw [tsum_mul_left,mul_comm]
    _ ≤ M*u^(p+1) := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hu.le hu1.le (Nat.succ_le_succ pe)) hM
  have add : f = fun v => g v+cut v := by
    funext v
    dsimp only [f,g,field,cut,remainder,posted,u]
    rw [Fin.sum_univ_castSucc (fun i : Fin (e+1+1) => (warm r:ℂ)^i.val*coeff i.val v)]
    simp only [Fin.val_castSucc,Fin.val_last]
    ring
  obtain ⟨conv,bill⟩ := del phase normPhase
  have convg : Summable g := conv
  have convCut : Summable cut := series.of_norm
  rw [add]
  refine ⟨convg.add convCut,?_⟩
  rw [convg.tsum_add convCut,add_mul]
  exact (norm_add_le _ _).trans (add_le_add bill cost)

/-- All fixed derivatives have a little-o signed Fourier remainder through
the actual public order p. One radius tail works for every unit phase.
The assay needs the stated analytic and tested wages on the same fields. -/
theorem original {G : Gauge} {warm : ℝ → ℝ} (hG : G.Simple) (paid : Coupling G warm)
    {read : ℝ → (Fin d → ℤ) → ℂ} {coeff : ℕ → (Fin d → ℤ) → ℂ}
    (b : Prices warm read coeff) (p : ℕ) (axis : Fin j → Fin d) (unit : Fin j → ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in trail, ∀ phase : (Fin d → ℤ) → ℂ, (∀ v, ‖phase v‖ ≤ 1) →
      let value := fun v => phase v*jet axis unit v*remainder (warm r) p (read r) coeff v
      Summable value ∧ ‖∑' v,value v‖ ≤ ε*warm r^p := by
  let q := p+1+12*(d+j+b.loss)
  have bought : Price read coeff axis unit warm p q :=
    WilsonOriginalCompactFourierRemainder.original hG paid b p axis unit
  have descend (k : ℕ) : Price read coeff axis unit warm p (p+k) →
      Price read coeff axis unit warm p p := by
    induction k with
    | zero => exact id
    | succ k ih => intro h;exact ih (withdraw hG paid b axis unit (Nat.le_add_right p k) h)
  have same : p+(q-p)=q := by dsimp [q];omega
  obtain ⟨C,hC,income⟩ := descend (q-p) (same.symm ▸ bought)
  have small := (WilsonOriginalTemperatureDecay.original paid).const_mul C
  rw [mul_zero] at small
  filter_upwards [income,paid.positive,(tendsto_order.mp small).2 ε hε] with r hr hu temp phase hphase value
  obtain ⟨conv,price⟩ := hr phase hphase
  refine ⟨conv,price.trans ?_⟩
  calc
    C*warm r^(p+1) = (C*warm r)*warm r^p := by rw [pow_succ];ring
    _ ≤ _ := mul_le_mul_of_nonneg_right temp.le (pow_nonneg hu.le _)

end YM.Integration.WilsonOriginalRecroppedShapeJets

