import YM.Integration.FVA1Physical.Sources.Round2.PhysicalFieldKernel
import YM.Integration.FVA1Physical.Wilson.ChartEnvelope
import YM.MSbar.Bout.Depart

/-! Absolute price for the literal independent inherited physical-field
stencil on an arbitrary gauge configuration, including its clipped chart
representative. Its polynomial dependence on the true coupling suffices
against an arbitrarily small posterior tail. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset MvPolynomial Lattice RG YM.Wilson Precision
open MSbar MSbar.Whisk MSbar.Bout MSbar.Mosaic MSbar.Measuring MSbar.Lis MSbar.Cacao MSbar.Bakery
open RGComparison.Core16.Spool YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology
variable {G : Gauge} {ι : Type} [Fintype ι]

theorem independentStencil_global (J : ι→Lamp G) (A : Issue G) (χ : ChartRatio G)
    {p m s : ℕ} {a B : ℝ} (b : Site A.c) (o : ι→Site A.f) (part : Bool)
    (ha : 0 ≤ a) (hg : |A.fClock| ≤ 1)
    (paid : ∀ i ≤ p, let f:=PowerSeries.coeff i (emittedRows A χ (jointFieldBank J A o part) p)
      f.totalDegree ≤ m ∧ Vault (Measuring.chart A.c G) {b} a s m 0 f B) (W : Config G A.c) :
    |independentStencil J A χ p o part W| ≤
      (p+1:ℕ)*(B*(1+|A.fClock⁻¹| *(LocalH.geom_patch G).choose)^(m+1)) := by
  let K:=|A.fClock⁻¹| *(LocalH.geom_patch G).choose
  let D:=B*(1+K)^(m+1)
  have entry (i : ℕ) (hi : i ≤ p) :
      |A.fClock^i * MvPolynomial.eval (chartLog A.fClock W)
        (PowerSeries.coeff i (emittedRows A χ (jointFieldBank J A o part) p))| ≤ D := by
    let f:=PowerSeries.coeff i (emittedRows A χ (jointFieldBank J A o part) p)
    obtain ⟨deg,base⟩:=paid i hi
    have cap:‖chartLog A.fClock W-0‖ ≤ K := by rw [sub_zero];exact chartLog_norm_bound .. 
    have hf:=Bout.looks ha (Bout.across (chartLog A.fClock W) base ha cap deg 0)
    rw [abs_mul,abs_pow]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg _) hg) (abs_nonneg _)).trans
      ((one_mul _).le.trans hf)
  unfold independentStencil
  apply (abs_sum_le_sum_abs ..).trans
  simpa only [sum_const,card_range,nsmul_eq_mul] using
    (sum_le_sum (s:=range (p+1)) (fun i hi=>entry i (Nat.le_of_lt_succ (mem_range.mp hi))))

end YM.Integration.FVA1Physical.Wilson
