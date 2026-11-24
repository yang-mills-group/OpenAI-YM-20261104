import YM.Integration.WilsonOriginalNullUnitFlow

/-! Exact rank-zero feeds at a physical stop, with the outstanding complete
original residual and the one true positive vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullUnitHistory
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit WheelP QuadraticLocal QuadraticLocal.Advent
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open WilsonOriginalNullCorridor WilsonOriginalNullFiledStep
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius

variable {G:Gauge} (R:Run G) {m N per k:ℕ}
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (W:∀ j,Rep G (R.family.side j per))
  (book:Concourse R.alloy R.kit R.T π Γ m N per k W)
local notation "C₀" => R.family
local notation "P₀" j:max => R.family.path.rep N per j
local notation "F₀" d:max => R.family.labels.level d
local notation "S₀" d:max => R.family.localSection d
local notation "κ" j:max => LocalComparison.forcedDivisor R.family j


include book in
theorem original (b n:ℕ) (ε:ℝ) (floor:m ≤ b) (live:b+n ≤ N)
    (o:∀ j,Site (R.family.side j per))
    (route:∀ j<n,o (b+j)=(R.family.path.levels.clock.op (b+j) per).ratio.parent (o (b+j+1)))
    (filed:∀ j<n,Filed R.family 0 N per (b+j) W (o (b+j+1)) ε)
    (h:Coefficient (F₀ 0) (R.family.side (b+n) per)) (B:ℝ) (form:h.Format (o (b+n)) R.family.params (W (b+n)))
    (paid:h.remBound (o (b+n)) (W (b+n)) (κ (b+n)) B)
    (null:projection (F₀ 0) R.family.params (W (b+n)).p.threshold (o (b+n)) h=0) :
    ∃ (v:Coefficient (F₀ 0) (R.family.side b per)) (a:ℕ→ℂ),v.Format (o b) R.family.params (W b) ∧
      v.remBound (o b) (W b) (κ b) (gain R.family b (b+n)*B) ∧
      projection (F₀ 0) R.family.params (W b).p.threshold (o b) v=0 ∧
      (∀ j<n,‖a j‖ ≤ ε*gain R.family (b+j) (b+n)*B) ∧
      flow R.family 0 N per b n (h.density (o (b+n)) (S₀ 0) (W (b+n)))=v.density (o b) (S₀ 0) (W b)+
        (∑ j∈Finset.range n,a j) • (fun U=>(W b).eval U:Config G (R.family.side b per)→ℂ) := by
  obtain ⟨v,α,shaped,amount,zero,price,read⟩:=WilsonOriginalNullPhysicalHistory.original R π Γ W book
    0 b n ε floor live o route filed h B form paid null
  let a (j:ℕ) : ℂ := α j 0
  refine ⟨v,a,shaped,amount,zero,fun j hj=>?_,read.trans ?_⟩
  · simpa only [a,WilsonOriginalNullUnitFlow.size] using price j hj
  · have base: b≤N:=by omega
    have point:=(book.1.walk b floor base).view
    have same : (fun U=>((W b).eval U:ℂ))=liftVac R.family.path N per b:=by
      funext U;change ((W b).eval U:ℂ)=((R.family.path.rep N per b).eval U:ℂ)
      exact_mod_cast congrFun point U
    rw [Finset.sum_smul,same]
    congr 1;apply Finset.sum_congr rfl;intro j hj
    have booked:=Finset.mem_range.mp hj
    rw [WilsonOriginalNullUnitFlow.raw]
    exact WilsonOriginalNullUnitFlow.vacuum R.family R.makes N per b j (a j) (by omega)

end YM.Integration.WilsonOriginalNullUnitHistory
