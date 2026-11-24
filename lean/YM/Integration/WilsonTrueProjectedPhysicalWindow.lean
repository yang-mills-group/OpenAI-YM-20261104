import YM.Integration.WilsonTrueProjectedWindowPrice

/-! A submitted finite Wilson source with a common upper field and funded
signed one-step returns. The projected error and the complete physical
remainder are recorded at the same lower appointment. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedPhysicalWindow
open Filter Finset MeasureTheory Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
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

theorem original (π₀ : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
    (Ψ : ∀ j, Rep G ((𝓒).side j p)) (course : Concourse R.alloy R.kit R.T π₀ Γ m N p k Ψ)
    {first stop : ℕ} (starts : m ≤ first) (active : first ≤ stop) (top : stop ≤ N)
    {γ ε : ℝ} (small : ε ≤ 1) (hm : Opened (𝓒) d first p)
    (opened : ∀ j ≥ first, j < stop → Opened (𝓒) d j p)
    (gates : ∀ j ≥ first, j < stop → Gate (𝓒) d N p j γ ε)
    (F : Spaces R p) (price spare : ℕ → ℝ)
    (fresh : ∀ j ≥ first, j < stop → WilsonTrueProjectedDualHistory.Signed R (N:=N) (d:=d) Ψ F j (price j))
    (old : ∀ j ≥ first, j < stop → HardReturn R (N:=N) (d:=d) Ψ j (spare j))
    (y : (𝓒).label d) (boundary cap : ℝ) (initial : Full R (N:=N) (d:=d) Ψ F stop y boundary)
    (initialCost : boundary ≤ cap) (capPos : 0 ≤ cap)
    (income : ∀ j ≥ first, j < stop → localBill R price spare j ≤ (1-(3:ℝ)^(-GermGraph.rate))*cap) :
    ∃ v, Full R (N:=N) (d:=d) Ψ F first v cap ∧
      σ (X first y-X first v) ≤ 4*((𝓒).S.a first/(𝓒).S.a stop)^(d+2)*cap ∧
      (first < stop → ∃ (s : store (𝓒) d p first) (a : ℝ), reads d N p first s a ∧
        F first =ᶠ[𝓝 1] V first s ∧ X first v = π first s) := by
  let W := fun j => wallet (𝓒) (localBill R price spare) boundary (stop-j) j
  obtain ⟨path,head,funded,earned⟩ := WilsonTrueProjectedPrimaryHistory.original R π₀ Γ Ψ course
    starts active top small opened gates F price spare fresh old y boundary initial
  have recursion (j : ℕ) (h : j < stop) : W j = decay (𝓒) j*W (j+1) + localBill R price spare j := by
    have dx : stop-j=(stop-(j+1))+1 := by omega
    simp only [W,dx,wallet]
  have capPaid (j : ℕ) (js : j ≤ stop) : first ≤ j → W j ≤ cap := by
    induction js using Nat.decreasingInduction with
    | self => intro _; simpa [W,wallet] using initialCost
    | of_succ j js ih =>
      intro fj
      have rho : decay (𝓒) j ≤ (3:ℝ)^(-GermGraph.rate) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast (𝓒).S.block_large j) (by norm_num [GermGraph.rate])
      have pos : 0 ≤ decay (𝓒) j := Real.rpow_nonneg (zero_le_one.trans (factor_positive (𝓒) j).le) _
      rw [recursion j js]
      calc
        _ ≤ (3:ℝ)^(-GermGraph.rate)*cap + (1-(3:ℝ)^(-GermGraph.rate))*cap :=
          add_le_add ((mul_le_mul_of_nonneg_left (ih (fj.trans j.le_succ)) pos).trans
            (mul_le_mul_of_nonneg_right rho capPos)) (income j fj js)
        _ = _ := by ring
  have charged (j : ℕ) (fj : first ≤ j) (js : j < stop) :
      σ (X j (path (j+1))-X j (path j)) ≤ cap := by
    obtain ⟨e,_,headCost,_⟩ := fresh j fj js
    have nn : 0 ≤ σ e.x := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have nonneg := nn.trans headCost
    have extra : 0 ≤ 4*stock (𝓒) j := mul_nonneg (by norm_num) (zero_le_one.trans (stage (𝓒) j).columns_ge)
    have cover := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right extra : (2:ℝ) ≤ 2+4*stock (𝓒) j) nonneg
    apply (earned j fj js).2.trans
    apply le_trans _ (capPaid j js.le fj)
    rw [recursion j js,localBill]
    linarith only [cover]
  have total := WilsonTrueProjectedWindowPrice.original (𝓒) R.makes hm active top opened path cap capPos charged
  rw [head] at total
  obtain ⟨s,h,r,B,rs,sz,hard,bill,form⟩ := funded first le_rfl active
  exact ⟨path first,⟨s,h,r,B,rs,sz,hard,bill.trans (capPaid first active le_rfl),form⟩,total,
    fun fs => (earned first le_rfl fs).1⟩

end YM.Integration.WilsonTrueProjectedPhysicalWindow
