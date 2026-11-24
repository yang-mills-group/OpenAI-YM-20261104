import YM.Integration.WilsonThermometerEarlierWallet
import YM.Integration.WilsonThermometerSolitaryExchange

/-! Linear hearings and absent occupations in the original three-slot test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerSolitaryReadWallet
open Function Filter Finset MeasureTheory Lattice RG Wilson Labels Source Work.G08 Next.Foundations
open Extra.Histories Extra.Histories.Relay MergeProof MergeProof.Accent Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Legato RG16 WilsonThermometerUnitFilingCoarse
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N per i u t:ℕ}
local notation "X" => Config G (R.family.side t per)
local notation "read" => reading R (N:=N)

open WilsonThermometerEarlierWallet Marker
local notation "J" => Stock.census (Fin 3)

theorem scaled {it:i≤t}{f:X→ℂ}{B:ℝ}(hf:Admitted (u:=u) (N:=N) R it f B)(c:ℂ):
    Admitted (u:=u) (N:=N) R it (c • f) (‖c‖*B):=by
  refine ⟨hf.1.smul c,fun j uj ji=>?_⟩
  rw [WilsonThermometerUnitFilingRawSum.scaled R c f hf.1 (ji.trans it),norm_mul]
  exact mul_le_mul_of_nonneg_left (hf.2 j uj ji) (norm_nonneg _)

theorem zero {it:i≤t}:Admitted (u:=u) (N:=N) R it (0:X→ℂ) 0:=by
  refine ⟨integrable_zero _ _ _,fun j _ ji=>?_⟩
  have e:=WilsonThermometerUnitFilingRawSum.scaled (N:=N) R (0:ℂ) (0:X→ℂ) (integrable_zero _ _ _) (ji.trans it)
  simp only [zero_smul,zero_mul] at e
  simp only [e,norm_zero,le_refl]

theorem collected {it:i≤t}{f:Fin 3→X→ℂ}{B:Fin 3→ℝ}
    (hf:∀v,Admitted (u:=u) (N:=N) R it (f v) (B v)):
    Admitted (u:=u) (N:=N) R it (∑v,f v) (∑v,B v):=by
  simp only [Fin.sum_univ_three]
  exact plus R (plus R (hf 0) (hf 1)) (hf 2)

theorem absent (a b:Fin 3→ℂ)(v:Fin 3)(s:(J).Mode)(away:v∉s.val):
    WilsonThermometerSolitaryExchange.share a b v s=0:=by
  unfold WilsonThermometerSolitaryExchange.share WilsonThermometerSolitaryExchange.token
  rw [Poly.part_mul]
  apply sum_eq_zero
  intro j _
  apply sum_eq_zero
  intro b' _
  split
  next merged =>
    by_cases is:b'=(J).fire v
    · subst b'
      exfalso
      apply away
      rw [←merged.2]
      exact mem_union_right _ (show v∈({v}:Finset _) from mem_singleton_self _)
    · rw [Poly.part_send,if_neg is,mul_zero]
  next => rfl

end YM.Integration.WilsonThermometerSolitaryReadWallet
