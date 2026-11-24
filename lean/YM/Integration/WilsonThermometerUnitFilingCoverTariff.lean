import YM.Integration.WilsonThermometerUnitFilingJointTensor
import YM.RegulatorIR.Budget.Channels

/-! Compute the rooted mark cost of an offered symmetric ordered derivative packet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCoverTariff
open Function Finset Lattice RegulatorIR Budget Budget.Packet Budget.Tuple
open WilsonThermometerUnitFilingJointMonomial WilsonThermometerUnitFilingJointTensor
open scoped ENNReal Classical BigOperators
variable {I Y Z:Type} [Fintype I] {k:ℕ} (c:Tuple (Option I) k→ℝ)
  (f:I↪Y){A:Tariff Z}(B:Premium A)(y:Y→Z)

theorem charged (r:ℕ)(w:∀ v,Tuple I v→ℝ)(pos:∀ v p,0≤w v p)
    (same:∀ v (e:Equiv.Perm (Fin v)) p,w v (p∘e)=w v p)
    (cover:∀ p:Tuple I r,(B.uses (y∘f)).width p≤ENNReal.ofReal (w r p)):
    markQ (B.uses y) (offer f (card c r)) ≤
      ENNReal.ofReal (∑ z:Tuple (Option I) k, w (length z) (name z)*|c z|):=by
  apply (mark_offer f).trans
  change (∑' p,‖card c r p‖ₑ * (B.uses (y∘f)).width p)≤_
  rw [tsum_fintype]
  suffices h : (∑ p,‖card c r p‖ₑ * (B.uses (y∘f)).width p)≤
      ENNReal.ofReal (∑ p,w r p*|card c r p|) from
    h.trans (ENNReal.ofReal_le_ofReal (price c r w pos same))
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _=>mul_nonneg (pos _ _) (abs_nonneg _))]
  apply Finset.sum_le_sum;intro p _
  calc
    _ ≤ ‖card c r p‖ₑ * ENNReal.ofReal (w r p):=mul_le_mul_right (cover p) _
    _ = _:=by rw [ENNReal.ofReal_mul (pos r p),← Real.norm_eq_abs,ofReal_norm,mul_comm]

end YM.Integration.WilsonThermometerUnitFilingCoverTariff
