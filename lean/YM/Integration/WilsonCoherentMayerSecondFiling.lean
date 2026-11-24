import YM.Integration.WilsonCoherentMayerSecondSource

/-! The complete returned density and its occupied parts at the second physical kernel. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerSecondFiling
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

open WilsonCoherentMayerSecondSource

def Joint (A:source) (Y:group→Poly (Γ)) : Prop :=
  ∀ x:TestSpace d,
    K₀ (deposit (N:=N) Q D u μ order A x)=K₀ (fun U=>Y U*Poly.pass (Mach (Γ) (operand Q D u μ order x U))) ∧
    ∀ (U:group) (s:(Γ).Mode),(deposit (N:=N) Q D u μ order A x U).part s=
      ∑ a:(Γ).Mode,∑ b:(Γ).Mode,if Poly.merges a b s then (Y U).part a*b.val.prod (operand Q D u μ order x U) else 0

theorem arrived (live:j+1≤N) (A:source) (Y:group→Poly (Γ)) (accepted:K₁ A=Y):
    Joint (N:=N) Q D u μ order A Y:=by
  intro x
  refine ⟨received Q D u μ order live A Y accepted x,?_⟩
  intro U s
  rw [mode Q D u μ order live A x U s,accepted]

end YM.Integration.WilsonCoherentMayerSecondFiling
