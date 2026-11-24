import YM.Integration.WilsonPhysicalDatedPinBudget
import YM.Integration.WilsonOriginalPublicNodalIndependent

/-! The matched independent term in the physical-pin budget on each
occupied subset, resolved into the actual paid K-stencil coordinates. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalNodalFigureTrials
open Function Filter Finset Lattice Wilson RG Labels Source Pert.Asymptotics Laurent
open XSpace XSpace.Cirrus PhysicalNext.Repeat.Legato RegulatorIR.FVAAlt2
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMovingForkMixedSeed (doses units)
open WilsonOriginalPublicPivotReflected (board evaluated)
open WilsonOriginalPublicNodalSeed (vector)
open WilsonOriginalPublicNodalIndependent (forecast)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)(W:Initialize G){n N per K:ℕ}(d:Fin n→ℕ)
  (file:Filed R d K)(Y:∀a,R.family.label (d a))(kn:K ≤ N)(node:Sample n)
  {h:Fin n→ℕ}(κ:(a:Fin n)→Knob (h a))(point:Fin n→Chamber)(S:Finset (Fin n))
local notation "w" => units R d K (doses R d file.station (N:=N) (per:=per) (file.A N per) Y)
local notation "g" => regulatorRun R.family N per K
local notation "α" => weight R d N per K (w) S
local notation "cash" q:max c:max => forecast R d κ point S node.layout node.F.p (W.tree node.F.p) q g c
local notation "figure" q:max => evaluated q g (board R W d (vector R d (N:=N) (per:=per) file Y) node S)

include kn
theorem original (q:ℕ):
    figure q=∑c:Selection R d S,α c*cash q c:=
  WilsonOriginalPublicNodalIndependent.valued R d κ point (p:=per) kn (w) S
    node.layout node.F.p (W.tree node.F.p) q g

theorem signed (q:ℕ)(T:Selection R d S→ℂ):
    (∑c:Selection R d S,α c*T c)-figure q=∑c:Selection R d S,α c*(T c-cash q c):=by
  rw [original R W d file Y kn node κ point S q]
  simp only [mul_sub,sum_sub_distrib]

theorem priced (q:ℕ)(T:Selection R d S→ℂ)(fare:Selection R d S→ℝ)
    (each:∀c,‖T c-cash q c‖ ≤ fare c):
    ‖(∑c:Selection R d S,α c*T c)-figure q‖ ≤ ∑c:Selection R d S,‖α c‖*fare c:=by
  rw [signed R W d file Y kn node κ point S q T]
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro c _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (each c) (norm_nonneg _)

end YM.Integration.WilsonPhysicalNodalFigureTrials
end
