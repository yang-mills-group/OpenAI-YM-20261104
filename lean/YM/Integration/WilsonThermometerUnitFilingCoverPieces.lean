import YM.Integration.WilsonThermometerUnitFilingCoverStock

/-! The original income and copied field restricted to the same finite subroster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCoverPieces
open Function Finset Gauge Lattice RG Wilson QuadraticLocal Marker QuadraticLocal.Earn Stationary
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonThermometerUnitFilingPinnedIncome WilsonEmittedRootedJetWage
open WilsonOriginalPaidWalkCover WilsonOriginalJointDeckMotion
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n N:Side} {o:Passport n Unit} {J:Census Unit} {I X:Type}
  (M:I→Row o J G X) (s:Finset I) (ht:n.val∣N.val) (page:Fin (Pages n N)) (t:X)

def pieces:↥s → Row o J G X:=fun i=>M i

theorem enrolled {w:Unit→ℝ}{grades:Unit→ℕ}{σ C:ℝ}{ord cap H:ℕ}
    (stock:Scene.Armada M w grades σ C ord cap H):
    Scene.Armada (pieces M s) w grades σ C ord cap H:=by
  refine ⟨stock.toMinistry,stock.positive,?_,
    ⟨fun i=>stock.purchases.spend i.val,fun i=>stock.purchases.usable i.val⟩,fun i=>stock.honor i.val⟩
  intro x
  have h:=stock.suggests x
  exact ⟨fun i=>h.1 i.val,h.2.1.comp_injective Subtype.val_injective,
    (tsum_comp_le_tsum_of_inj h.2.1 h.1 Subtype.val_injective).trans h.2.2⟩

theorem submitted (a:ℂ→ₗ[ℝ]ℝ) (z:Joint G N):
    WilsonThermometerUnitFilingCoverStock.portrait M s
      (fun i=>a ((M i).paint t)) 0 z.1 (expandAt (locus ht page o) (RG.increment 1 z.2))=
    a (WilsonOriginalMixedCoveredRead.field ht (pieces M s) t page (fun _=>True) z):=by
  rw [WilsonThermometerUnitFilingCoverStock.copied]
  unfold WilsonOriginalMixedCoveredRead.field
  simp only [if_true,tsum_fintype,pieces,map_sum]
  rw [← Finset.sum_attach s]
  apply Finset.sum_congr rfl;intro i _
  rw [(place ht page (M i.val)).1]
  rw [mul_comm (M i.val |>.paint t),← Complex.real_smul,map_smul,smul_eq_mul,mul_comm]
  rfl

theorem wage {w:Unit→ℝ}{grades:Unit→ℕ}{σ C β δ:ℝ}{ord cap H:ℕ}
    (stock:Scene.Armada M w grades σ C ord cap H)(seed:0<σ)(tiny:0<δ)
    (late:Real.exp 1 ≤ β)(paid:Real.exp (σ⁻¹^2) ≤ β)(r u:ℕ)(test:Finset (Fin r → Slot G N)):
    w () * ∑y∈test,premium ht page o u y *
      ‖entry r (WilsonThermometerUnitFilingPinnedIncome.envelope ht (pieces M s) page t 0) y‖ ≤
      WilsonThermometerUnitFilingMomentSale.price G r u δ * β^δ*C:=
  charged ht (pieces M s) page (enrolled M s stock) seed tiny late paid t 0 r u test

end YM.Integration.WilsonThermometerUnitFilingCoverPieces
