import YM.Integration.WilsonOriginalProjectedCurvatureFoundry
import YM.Integration.WilsonMovingMentorFoundryTransport

/-! Deposit independently entered Q marks into the actual first output before the second original kernel. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerSecondSource
open Finset Lattice Wilson RG Source Labels Marker Ac LocalComparison Global
open PhysicalNext.Repeat.Legato Comparison.Density.RenderM MergeProof.Accent FVA1 MeasureTheory
open ActualOriginalQReaders ActualOriginalQPackets
open scoped BigOperators Classical

variable {G:Gauge} {R:Run G} {B:MS.Local.Physical.Deck G}
  {V:Type} [Fintype V] [DecidableEq V] {j N per n:ℕ} {hn:n≤j+1}
  (Q:MS.Land.Prescription B) (D:ActualRunQlocalNativeTuple.Datum R per (j+1) n hn V)
  (u:V→MS.Rake.Label B) (μ:ℝ) (order:V→ℕ)
local notation "Γ" => Stock.census V
local notation "g" => Pert.Asymptotics.regulatorRun R.family N per (j+1)
local notation "d" => ActualRunQlocalNativeTuple.orbit D
local notation "K₁" => LocalComparison.actualPush R.family N per (j+1)
local notation "K₀" => LocalComparison.actualPush R.family N per j
local notation "S" => R.family.path.levels.clock.op j per
local notation "β" => R.family.path.β N per (j+1)
local notation "group" => Config G (R.family.side (j+1) per)
local notation "source" => Config G (R.family.side (j+1+1) per)→Poly (Stock.census V)

def operand (x:TestSpace d) (U:group) (v:V):ℂ:=
  ActualRunQlocalNativeTuple.reader D v (x v) *
    ActualOriginalCalibratedColumns.weightedObservable R B Q (u v) μ (R.family.side (j+1) per)
      (ActualRunQlocalNativeTuple.root D v) U (order v)

def deposit (A:source) (x:TestSpace d) (U:group):Poly (Γ):=
  (K₁ A U) * Poly.pass ((ActualOriginalQPackets.packets Q D u μ order N).read x g U)

theorem field (live:j+1≤N) (A:source) (x:TestSpace d) (U:group) :
    deposit (N:=N) Q D u μ order A x U = (K₁ A U)*Poly.pass (Mach (Γ) (operand Q D u μ order x U)) := by
  unfold deposit operand
  rw [ActualOriginalQPackets.source_factor Q D u μ order N live]

theorem mode (live:j+1≤N) (A:source) (x:TestSpace d) (U:group) (s:(Γ).Mode):
    (deposit (N:=N) Q D u μ order A x U).part s =
      ∑ a:(Γ).Mode,∑ b:(Γ).Mode, if Poly.merges a b s then
        (K₁ A U).part a * ∏ v∈b.val,operand Q D u μ order x U v else 0:=by
  rw [field Q D u μ order live A x U,Poly.part_mul]
  simp only [Mach,Extra.Trajectories.pass_fire]

theorem integral (live:j+1≤N) (A:source) (x:TestSpace d)
    (integrable:Integrable (deposit (N:=N) Q D u μ order A x) (prior G _))
    (W:Config G (R.family.side j per)) (s:(Γ).Mode):
    (K₀ (deposit (N:=N) Q D u μ order A x) W).part s =
      ∫U, ((S).density β U W) • (∑ a:(Γ).Mode,∑ b:(Γ).Mode, if Poly.merges a b s then
        (K₁ A U).part a * ∏ v∈b.val,operand Q D u μ order x U v else 0) ∂prior G _:=by
  have hu:=StepData.push_slice (R.family.path.levels.transition_mass j per β) W _ integrable
  change (Poly.get s) (∫U, ((S).density β U W) • deposit (N:=N) Q D u μ order A x U ∂prior G _) = _
  rw [←(Poly.get s).integral_comp_comm hu]
  apply integral_congr_ae
  filter_upwards with U
  change ((S).density β U W) • (deposit (N:=N) Q D u μ order A x U).part s=_
  rw [mode Q D u μ order live A x U s]

/-- Substituting the certified first output occurs under the genuine second kernel. -/
theorem received (live:j+1≤N) (A:source) (Y:group→Poly (Γ)) (arrived:K₁ A=Y)
    (x:TestSpace d) :
    K₀ (deposit (N:=N) Q D u μ order A x)=K₀ (fun U=>Y U*Poly.pass (Mach (Γ) (operand Q D u μ order x U))):=by
  apply congrArg K₀
  funext U
  rw [field Q D u μ order live A x U,arrived]

end YM.Integration.WilsonCoherentMayerSecondSource
