import YM.Integration.WilsonThermometerRelativeWard

/-! The exact native regrading of a deposited Haar equation, with its signed calibration and tariff. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerPhysicalEquationInvoice
open Function Filter Finset Lattice Wilson RG Labels Source Push Extraction RG12 RG17 Climb Trace.Pilot
open MergeProof Next.Extract PhysicalNext.Repeat.Legato PhysicalNext.Repeat Legato Bandage
open WilsonThermometerRelativeWard
open scoped Classical Topology
variable {G : Gauge} (R : Run G)
variable {E : ∀ d, SectionData (R.family.labels.level d)} (W : Mark.Weave G)
  (P : ∀ d, (ℕ×ℕ) → (R.family.label d ≃ₗ[ℂ] R.family.label d)) {b : Presentation R.family}

theorem restored {d N p : ℕ} (x y : R.family.label d) (q : Label G d)
    (posted : bindP R.family W d N p (P d (N,p)) q = x-y) :
    gap R P (N:=N) (p:=p) x y = Mark.tied R.family d N ((R.family.labels.level d).coords (W d q)) := by
  simp only [gap,←posted,bindP,Astar,Mark.embedTo,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]

theorem paid {d N : ℕ} (q : Label G d) :
    (R.family.labels.level d).coeffSize
        (Mark.tied R.family d N ((R.family.labels.level d).coords (W d q))) ≤
      (R.family.labels.level d).coeffSize ((R.family.labels.level d).coords (W d q)) := by
  let L:=R.family.labels.level d
  let t:=R.family.path.levels.clock.threshold N
  have small : t ≤ 1 := (R.family.path.levels.budget N).threshold_le
  have nonneg : 0≤t := (Mark.positive_t R.family N).le
  apply Finset.sum_le_sum
  intro j _
  let u := L.coords (W d q)
  change ‖(↑(t^(L.grades j).2):ℂ)*u j‖ ≤ ‖u j‖
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ nonneg small)

theorem issued (house : Hearthside R.family E W P b (Bandage.fly R.alloy.B.a))
    {d N p : ℕ} (x y : R.family.label d) (q : Label G d) (law : q∈Maxwell.equationIdeal G d)
    (posted : bindP R.family W d N p (P d (N,p)) q = x-y) :
    b.step d (N,p) x=b.step d (N,p) y ∧ (R.family.labels.level d).coeffSize (gap R P (N:=N) (p:=p) x y) ≤
      (R.family.labels.level d).coeffSize ((R.family.labels.level d).coords (W d q)) := by
  have lifted : x-y ∈ LinearMap.ker (b.step d (N,p)).toLinearMap := by
    rw [(house.foundation.step d N p).ker]
    exact ⟨q,law,posted⟩
  refine ⟨?_,?_⟩
  · have h := LinearMap.mem_ker.mp lifted
    change b.step d (N,p) (x-y) = 0 at h
    simpa only [map_sub,sub_eq_zero] using h
  · rw [restored R W P x y q posted]
    exact paid R W q

end YM.Integration.WilsonThermometerPhysicalEquationInvoice
