import YM.Integration.WilsonPhysicalExteriorIndependentPrice

/-! The signed coefficient difference of the actual independently
transported word, with its genuine finite coupling convolution and
the engineering price applied before any cancellation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorCompensatedQuote
open Function Finset Matrix PowerSeries Lattice
open MS MS.Land MS.Menus MS.Rake FVAAlt2 Lobby
open WilsonPhysicalExteriorIndependentPrice WilsonPhysicalExteriorIndependentWord
open WilsonPhysicalExteriorRegisteredRows
open scoped BigOperators Classical
variable {G:Gauge}{B:MS.Local.Physical.Deck G}{W:Type} [Fintype W]
local notation "PS" => PowerSeries ℂ
variable (Q:Prescription B)

def total (d:W→ℕ) (b:(i:W)→Plaid B (d i)) (v:W→ℝ) (y z:ℝ) (k:ℕ)
    (E:Array B d→ℕ→ℂ) : ℂ :=
  ∑a:Array B d,∑r∈antidiagonal k,coeff r.1 (rate Q (labels d b) v y z a)*E a r.2

theorem signed (d:W→ℕ) (b:(i:W)→Plaid B (d i)) (v:W→ℝ) (y z:ℝ) (k:ℕ)
    (F X:Array B d→PS) : total Q d b v y z k (fun a j=>coeff j (F a)-coeff j (X a)) =
      coeff k ((∑a:Array B d,rate Q (labels d b) v y z a*F a)-
        ∑a:Array B d,rate Q (labels d b) v y z a*X a) := by
  simp only [total,map_sub,map_sum,coeff_mul,←sum_sub_distrib,←mul_sub]

/-- One price before all input and output labels on the fixed finite
register. It controls the signed joint perturbative report even for
separately normalized fields. -/
theorem paid (d:W→ℕ) (L:ℕ) : ∃ A:ℝ,0≤A ∧ ∃m:ℕ,
    ∀ b:(i:W)→Plaid B (d i),∀ v:W→ℝ,∀ y z H ε:ℝ,0≤H→0≤ε→∀ E:Array B d→ℕ→ℂ,
    (∀a,∀j≤L,H*‖E a j‖≤ε) →
    H*‖total Q d b v y z L E‖≤A*(length (clock v y z))^m*ε := by
  obtain ⟨C,hC,m,p⟩:=WilsonPhysicalExteriorIndependentPrice.paid Q d L
  let I:=Array B d
  let D:=antidiagonal L
  refine ⟨(Fintype.card I:ℝ)*(D.card:ℝ)*C,by positivity,m,?_⟩
  intro b v y z H ε hH he E hE
  let cost:=C*(length (clock v y z))^m
  have hc:0≤cost:=by
    have hl:0≤length (clock v y z):=by unfold length;positivity
    exact mul_nonneg hC (pow_nonneg hl _)
  calc
    H*‖total Q d b v y z L E‖ ≤ ∑a:I, H*‖∑r∈D,coeff r.1 (rate Q (labels d b) v y z a)*E a r.2‖ := by
      rw [←mul_sum];exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hH
    _ ≤ ∑a:I,∑r∈D,cost*ε := by
      apply sum_le_sum;intro a _
      calc
        _≤H*(∑r∈D,‖coeff r.1 (rate Q (labels d b) v y z a)*E a r.2‖) :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) hH
        _≤_:=by
          rw [mul_sum];apply sum_le_sum;intro r hr
          have h:=mem_antidiagonal.mp hr
          rw [norm_mul,mul_left_comm]
          exact mul_le_mul (p b a r.1 (by omega) v y z) (hE a r.2 (by omega))
            (mul_nonneg hH (norm_nonneg _)) hc
    _=_:=by simp [cost,D,I,nsmul_eq_mul];ring

end YM.Integration.WilsonPhysicalExteriorCompensatedQuote
end
