import YM.Integration.WilsonMeasuredProtectedSiteFare

/-! The paid nonzero tariff support is countable even when a submitted family contains uncountably many blank rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredChargedSiteFare
open Filter Function Finset Lattice RG Wilson Source Labels Push.Local Planned.GuardedAtom
open Push.AbsoluteSums WilsonCenteredCaptureSlots WilsonCenteredFailedHalo WilsonCenteredMountedCapture
open Trace.Physical PhysicalNext Repeat Legato Roost Org Pert.Asymptotics
open Push.PriceCompiler AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset
open scoped Classical Topology BigOperators

variable {G:Gauge} (R:Run G)
local notation "B" => R.family.path.levels
local notation "A" => R.family
local notation "divisor" => LocalComparison.forcedDivisor R.family

theorem original (simple:G.Simple) (d n q:ℕ) {C ε:ℝ} (hc:0<C) (ep:0<ε) :
    ∀ᶠ i:ℕ in atTop, ∀ (m N per k probe:ℕ) (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
      (Ψ:(j:ℕ)→Rep G ((A).side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per k Ψ → m ≤ i → i < N → probe ≤ i →
    ∀ (y:Site ((A).side i per)) (ι:Type) (T:ι→Support ((A).side i per)) (f:ι → Config G ((A).side i per)→ℂ)
      (e E:ι→ℝ) (a b M:ℝ), 0<M →
    (∀ s,y∈T s) → (∀ s,(Ψ i).p.Regular (T s) (f s)) →
    SumBudget (fun s=>reservedMass (Ψ i).p (T s) (e s)) a →
    SumBudget (fun s=>reservedMass (Ψ i).p (T s) (E s)) b →
    (∀ s,(Ψ i).p.supBounds y (T s) (f s) (e s)) → (∀ s U,‖f s U‖≤E s) →
    b≤(C*(B).clock.hatBeta i^n)*M →
    factor (A).params ((A).localSection d) (Ψ i).p.supportExponent ((B).params i).columns*a ≤
      (ε*(regulatorRun (A) N per probe)^q)*M →
    ∃z:Coefficient ((A).labels.level d) ((A).side i per),
      (z.Format y (A).params (Ψ i) ∧ z.remBound y (Ψ i) (divisor i)
        (3*(ε*(regulatorRun (A) N per probe)^q)*M)) ∧
      ((A).labels.level d).coeffSize z.x≤(ε*(regulatorRun (A) N per probe)^q)*M ∧
      ∀U,z.density y ((A).localSection d) (Ψ i) U=((Ψ i).eval U:ℂ)*(∑' s,f s U) :=by
  filter_upwards [WilsonMeasuredProtectedSiteFare.original R simple d n q hc ep]
    with i returner m N per k probe π Γ Ψ course before cut report y ι T f e E a b M hM
  intro roots regular soft hard tested crude gross good
  let S:Set ι:=Function.support (fun s=>reservedMass (Ψ i).p (T s) (E s))
  letI : Countable S:=hard.2.1.countable_support.to_subtype
  obtain ⟨Q,fm,prim,read⟩:=returner m N per k probe π Γ Ψ course before cut report y S
    (fun s=>T s.val) (fun s=>f s.val) (fun s=>e s.val) (fun s=>E s.val) a b M hM
    (fun s=>roots s.val) (fun s=>regular s.val) (sumBudget_subtype (·∈S) soft)
    (sumBudget_subtype (·∈S) hard) (fun s=>tested s.val) (fun s=>crude s.val) gross good
  refine ⟨Q,fm,prim,fun U=>(read U).trans (congrArg (((Ψ i).eval U:ℂ)*·) ?_)⟩
  apply tsum_subtype_eq_of_support_subset (f:=fun s=>f s U) (s:=S)
  intro s hs
  change reservedMass (Ψ i).p (T s) (E s) ≠ 0
  rw [reservedMass]
  apply mul_ne_zero (Real.exp_ne_zero _)
  intro hz
  apply hs
  exact norm_eq_zero.mp (le_antisymm ((crude s U).trans hz.le) (norm_nonneg _))

end YM.Integration.WilsonMeasuredChargedSiteFare
end
