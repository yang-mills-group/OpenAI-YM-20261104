import YM.Integration.QLocalThermalJoinedRate
import YM.Integration.WilsonRootedTwoDateHardRadius

/-! The actual joined tariff and both marked bills at a common finite radius. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateHardMargins
open Function Finset Lattice RG Wilson Marker Overlay RG3.Script.Picnic LocalComparison LocalComparison.Global
open ActualWilsonDirtyPartners QLocalThermalJoinedRate WilsonRootedTwoDateHardRadius
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X : Type} [DecidableEq V] [Fintype V]
  {Γ : Census V} {D : V→ ComparisonDensity.Address.Orbit} {Q : Rep G n} {o : V→Site n}
  {p : BudgetPoint} (P : MarkedPackets D G n Γ) {a : V→Support n}
  {region : Comparison.Density.Testing.Region (fun v=>(D v).Mood) n} {g width amount κ k d τ : ℝ}
  {off cov : ℕ} (T : Taste X o Q Γ)

local notation "oneW" => fun _ : V=>(1:ℝ)
local notation "modes" => (Fintype.card Γ.Mode:ℝ)
local notation "marks" => (Fintype.card V:ℝ)

theorem sold (H : P.Paid p a region (oneW) g width amount off cov)
    (old : ForcedBudget p T (smaller τ (oneW)) κ d) (ht : 0<τ) (hu : τ≤1)
    (headroom : 2*k*blockSites p.B≤p.supportExponent) :
    ∃s : ℝ,0<s ∧ s≤1 ∧ let radii := smaller s (smaller τ (oneW))
      P.Paid p a region radii g width (s*(τ*amount)) off cov ∧
      Nonempty (ForcedBudget p T radii κ (s*d)) ∧
      2*(k+(marks)*(κ*(s*d)))*blockSites p.B≤3*p.supportExponent/2 ∧
      2*(marks)*(modes)*charge P p off (s*(τ*amount))≤1 ∧
      ∀ z : Γ.Mode, ((s*τ)^z.val.card)⁻¹*Poly.toll radii z=1 := by
  let bill := 2*(marks)*(modes)*charge P p off (τ*amount)
  obtain ⟨s,pos,one,small,fee⟩ := margins (b:=d) (Q:=bill) (blockSites p.B) (marks) κ p.exponent_pos headroom
  have prior := packets P H ht hu
  refine ⟨s,pos,one,packets P prior pos one,⟨compulsory T old prior.positive pos one⟩,small,?_,?_⟩
  · convert fee using 1
    dsimp [bill,charge]
    ring
  · intro z
    simp [smaller,Poly.toll,pos.ne',ht.ne']

end YM.Integration.WilsonRootedTwoDateHardMargins
