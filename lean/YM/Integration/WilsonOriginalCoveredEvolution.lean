import YM.Integration.WilsonOriginalCopiedHistory

/-! The finite reporting history is computed from its independently registered entrance and dated formal couplings. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCoveredEvolution
open WilsonOriginalCopiedHistory
open FVA1Physical.TwoReset
open Function Filter Finset Lattice RG Precision Tree YM.Wilson QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Sunrise Comparison Comparison.RG02 Comparison.RG02.Bulk
open Next.SectorChange Marker Multi PertExtension.Series Extra.Trajectories
open AllOrder AllOrder.Floe Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] {W : Census V}

/-- The additive kinetic correction has zero constant term at each enrolled date. -/
def increment (coin : Pace.Coin) : Pace.Coin := fun i=> if i=0 then 0 else coin i

private theorem starts (coin : Pace.Coin) : increment coin 0=0 := by simp [increment]

theorem measured (coin : Pace.Coin) (zero : coin 0=0) : increment coin=coin := by
  funext i
  by_cases hi : i=0
  · subst i; simp [increment,zero]
  · simp [increment,hi]

variable (R : Run G) {N b per : ℕ} (inlet : b<N)
  (π : ℕ→Layout G) (Γ : ℕ→Pace.Coin) (depth p : ℕ) (grades : V→ℕ)
  (top : Values G W (R.family.side b per))

/-- At the registered top the full table is supplied once. Each preceding date uses its own vacuum and kinetic reset. -/
def run (i : ℕ) (ib : i≤b) : Values G W (R.family.side i per) :=
  if eq : i=b then eq ▸ top else
    block R (ib.trans_lt inlet) p (receive (run (i+1) (by omega)) (π (i+1)) (AllOrder.Floe.Step.tape depth)
      grades (increment (Γ (i+1))) (starts _) depth p)
termination_by b-i

theorem head : run R inlet π Γ depth p grades top b le_rfl=top := by rw [run]; simp

theorem next (i : ℕ) (ib : i<b) :
    run R inlet π Γ depth p grades top i (Nat.le_of_lt ib) =
      block R (ib.trans inlet) p (receive (run R inlet π Γ depth p grades top (i+1) (Nat.succ_le_iff.mpr ib))
        (π (i+1)) (AllOrder.Floe.Step.tape depth) grades (increment (Γ (i+1))) (starts _) depth p) := by
  rw [run, dif_neg (Nat.ne_of_lt ib)]

omit [Fintype V] in
private theorem restore {n : Side} (bank : Values G W n) (quiet : Layout G) (grades : V→ℕ) (h p : ℕ)
    {a c : Pace.Coin} (same : a=c) (ha : a 0=0) (hc : c 0=0) :
    receive bank quiet (AllOrder.Floe.Step.tape h) grades a ha h p =
      receive bank quiet (AllOrder.Floe.Step.tape h) grades c hc h p := by subst c; rfl

/-- On an authenticated date this is the original coin including its whole measured higher part. -/
theorem actual (i : ℕ) (ib : i<b) (zero : Γ (i+1) 0=0) :
    run R inlet π Γ depth p grades top i (Nat.le_of_lt ib) =
      block R (ib.trans inlet) p (receive (run R inlet π Γ depth p grades top (i+1) (Nat.succ_le_iff.mpr ib))
        (π (i+1)) (AllOrder.Floe.Step.tape depth) grades (Γ (i+1)) zero depth p) := by
  refine (next R inlet π Γ depth p grades top i ib).trans ?_
  exact congrArg (block R (ib.trans inlet) p) (restore _ _ _ _ _ (measured (Γ (i+1)) zero) _ zero)

end YM.Integration.WilsonOriginalCoveredEvolution
