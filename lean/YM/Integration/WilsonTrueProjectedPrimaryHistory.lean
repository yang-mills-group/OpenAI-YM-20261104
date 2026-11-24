import YM.Integration.WilsonTrueProjectedPrimaryReturn

/-! Keep the actual incoming coordinate at the upper date. Each step
has its own measured field and its own signed primary feed. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedPrimaryHistory
open Function Filter Finset MeasureTheory Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
open Extra.Histories Extra.Histories.Relay Bid MergeProof Org QuadraticLocal QuadraticLocal.Advent
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP
open PhysicalNext Repeat Legato Graces Roost
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonTrueProjectedColumnDescent WilsonTrueProjectedDualHistory
open scoped Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} (R : Run G) {d m N p k : ℕ}
local notation "𝓒" => R.family
local notation "σ" => ((𝓒).labels.level d).coeffSize
local notation "X" => measuring (𝓒) d N p
local notation "π" => page (C:=𝓒) d p
local notation "V" => value (C:=𝓒) d N p
local notation "Q" => store (𝓒) d p

/-- The stored coordinates belong to one physical cutoff. The coefficient
at the upper end is the one submitted to the Wilson kernel. Every intervening
change is measured in the original receiving frame. -/
theorem original (π₀ : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
    (Ψ : ∀ j, Rep G ((𝓒).side j p)) (course : Concourse R.alloy R.kit R.T π₀ Γ m N p k Ψ)
    {first stop : ℕ} (starts : m ≤ first) (active : first ≤ stop) (top : stop ≤ N)
    {γ ε : ℝ} (small : ε ≤ 1)
    (opened : ∀ j ≥ first, j < stop → Opened (𝓒) d j p)
    (gates : ∀ j ≥ first, j < stop → Gate (𝓒) d N p j γ ε)
    (F : Spaces R p) (price spare : ℕ → ℝ)
    (fresh : ∀ j ≥ first, j < stop → WilsonTrueProjectedDualHistory.Signed R (N:=N) (d:=d) Ψ F j (price j))
    (old : ∀ j ≥ first, j < stop → HardReturn R (N:=N) (d:=d) Ψ j (spare j))
    (y : (𝓒).label d) (boundary : ℝ) (initial : Full R (N:=N) (d:=d) Ψ F stop y boundary) :
    let W := fun j => wallet (𝓒) (localBill R price spare) boundary (stop-j) j
    ∃ path : ℕ → (𝓒).label d, path stop = y ∧
      (∀ j ≥ first, j ≤ stop → Full R (N:=N) (d:=d) Ψ F j (path j) (W j)) ∧
      ∀ j ≥ first, j < stop →
        (∃ (s : Q j) (M : ℝ), reads d N p j s M ∧ F j =ᶠ[𝓝 1] V j s ∧ X j (path j) = π j s) ∧
        σ (X j (path (j+1))-X j (path j)) ≤ decay (𝓒) j*W (j+1)+2*price j+spare j := by
  intro W
  let statement (j : ℕ) :=
    ∃ path : ℕ → (𝓒).label d, path stop = y ∧
      (∀ l ≥ j, l ≤ stop → Full R (N:=N) (d:=d) Ψ F l (path l) (W l)) ∧
      ∀ l ≥ j, l < stop →
        (∃ (s : Q l) (M : ℝ), reads d N p l s M ∧ F l =ᶠ[𝓝 1] V l s ∧ X l (path l) = π l s) ∧
        σ (X l (path (l+1))-X l (path l)) ≤ decay (𝓒) l*W (l+1)+2*price l+spare l
  have descend (j : ℕ) (js : j ≤ stop) : first ≤ j → statement j := by
    induction js using Nat.decreasingInduction with
    | self =>
      intro _
      refine ⟨fun _ => y,rfl,?_,?_⟩
      · intro l sl ls
        have eq : l=stop := le_antisymm ls sl
        subst l
        simpa [W,wallet] using initial
      · intro l sl ls
        omega
    | of_succ j js ih =>
      intro fj
      obtain ⟨path,head,fund,earned⟩ := ih (fj.trans j.le_succ)
      obtain ⟨v,step,sectionRead,primary,_⟩ := WilsonTrueProjectedPrimaryReturn.original R π₀ Γ Ψ course
        (starts.trans fj) (js.trans_le top) (opened j fj js) small (gates j fj js) F (path (j+1))
        (fund (j+1) le_rfl js) (fresh j fj js) (old j fj js)
      let next := Function.update path j v
      have stay {l : ℕ} (larger : j < l) : next l = path l := Function.update_of_ne larger.ne' _ _
      have new : next j = v := Function.update_self ..
      have cost : W j = decay (𝓒) j*W (j+1)+(2+4*stock (𝓒) j)*price j+spare j := by
        have count : stop-j=(stop-(j+1))+1 := by omega
        simp only [W,count,wallet,localBill]
        ring
      refine ⟨next,(stay js).trans head,?_,?_⟩
      · intro l jl ls
        rcases jl.eq_or_lt with eq | lt
        · subst l
          rwa [new,cost]
        · rw [stay lt]
          exact fund l lt ls
      · intro l jl ls
        rcases jl.eq_or_lt with eq | lt
        · subst l
          rw [new,stay (Nat.lt_succ_self j)]
          exact ⟨sectionRead,primary⟩
        · rw [stay lt,stay (lt.trans l.lt_succ_self)]
          exact earned l lt ls
  exact descend first active le_rfl

end YM.Integration.WilsonTrueProjectedPrimaryHistory
