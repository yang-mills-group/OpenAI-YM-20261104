import YM.Integration.WilsonThermometerWeakSpatialGrowth

/-! A finite coupling-power price at the true positions buys the same physical
engineering exponent at each finite derivative order and on each compact. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakGrossCoupling
open Set Filter Spec Trace.Pilot OPE OPE.Orbits PhysMS PhysMS.Frame
open WilsonThermometerWeakValueRecovery
open scoped Classical Topology ContDiff
variable {G:Gauge} {n:ℕ} {U:Set (Points n)} {Y:Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem paid (simple:G.Simple)(g:ℝ→ℝ)(linked:Coupling G g)(A:ℝ)(positive:0<A)
    (F:ℝ→Points n→Y)(j:ℕ)
    (kernels:∀K,IsCompact K→K⊆U→∃(b:ℕ)(C:ℝ),0≤C ∧ ∀ᶠr in trail,∀x∈K,
      ‖iteratedFDeriv ℝ j (F r) x‖≤C*(g r^b)⁻¹):
    Price trail U F (fun r=>r^(-A)) 1 j:=by
  intro K compact inside
  obtain ⟨b,C,Cn,earned⟩:=kernels K compact inside
  have small:=subpower_payment linked simple 1 A positive 1 zero_lt_one b
  refine ⟨C,Cn,?_⟩
  filter_upwards [earned,small,self_mem_nhdsWithin (a:=0)] with r h s rp x hx
  rw [one_mul,one_mul] at s
  rw [pow_one,Real.rpow_neg rp.le]
  exact (h x hx).trans (mul_le_mul_of_nonneg_left (inv_anti₀ (Real.rpow_pos_of_pos rp A) s) Cn)

end YM.Integration.WilsonThermometerWeakGrossCoupling
end
