import YM.Integration.WilsonPositionProgramOriginalTrial

/-! The actual variable-block Wilson field dictionary is evaluated on the
same finite normalized period used for the separated position publication. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramOriginalLanding
open Precision Next.Foundations
open Filter Function Set Finset Metric Lattice RG PhysicalNext.Repeat.Legato
open MS MS.Rake MS.Land MS.Dial MS.Tide MS.Orbit MS.Vista
open RegulatorIR.FVAAlt2 YM.FVAAlt2 XSpace XSpace.Cirrus XSpace.Expense
open FVA2 FVA2.Arrival FVA2.Arrival.Schedule FVA2.Notch
open scoped Classical Topology
variable {G : Gauge} (C : Run G)
variable {n : ℕ} {O : Booked (Press.portDeck G)} (M : MS_Data G O)
variable (Q : Prescription (Press.portDeck G)) (labels : Fin n→Label (Press.portDeck G))
variable (μ : ℝ) (k : ℕ) (K : Set (Points n)) (compact : IsCompact K) (sep : K⊆conf n)
local notation "ρ" => (1/16:ℝ)
local notation "T" => Flight.trail ρ K μ

def opened (v : Sample n) : ℂ := PowerSeries.coeff k
  (Lobby.newEra (chart G) (Lodge.basisR C) Q (μ+Real.log v.F.spacing) labels
    (wrap v.F.p.side ∘ v.layout) v.F.spacing)

theorem located (f : Flight ρ K) :
    Lobby.evaluateR (chart G) (Lodge.basisR C) Q labels T μ k f =
      opened C Q labels μ k f.sample := by
  let v := f.sample
  let head := (T).head f
  let off := fun i => (T).off i f
  have sites (i : Fin n) : wrap v.F.p.side (head+off i) = wrap v.F.p.side (v.layout i) := by
    rw [map_add, ← psi_back v.F]
    rw [show wrap (periodN (psi v.F)) head=wrap (periodN (psi v.F)) f.peg from wrap_lift _]
    change wrap (periodN (psi v.F)) f.peg+wrap (periodN (psi v.F)) (v.layout i-f.peg)=_
    rw [map_sub]
    abel
  change PowerSeries.coeff k (Lobby.newEra (chart G) (Lodge.basisR C) Q (μ-theta v.F) labels
    (fun i => wrap (periodN (psi v.F)) (head+off i)) (Real.exp (-theta v.F))) = _
  rw [bornS f.signs.2.2.1,theta_value f.signs.2.2.1,sub_neg_eq_add,psi_back,
    show (fun i => wrap v.F.p.side (head+off i)) = wrap v.F.p.side ∘ v.layout from funext sites]
  rfl

include compact sep in
theorem flight (simple : G.Simple)
    (paid : TaylorOKPl M (Lobby.Table (Lodge.basisR C) (Press.portDeck G)) Q) :
    ∃ B : ℝ, 0<B ∧ ∀ᶠ f : Flight ρ K in Pitch.go ρ K,
      ‖opened C Q labels μ k f.sample - tour M labels μ (plot (familiar f.sample)) univ k‖ ≤
      B * (f.sample.F.spacing^Tide.mildG) := by
  have h := (Lobby.pays_all (chart G) (Lodge.basisR C) Q labels M
    (chart_ok G) (WilsonPositionProgramOriginalTrial.uses K compact sep μ) simple paid).pay k
  obtain ⟨B,pos,read⟩ := h.2
  refine ⟨B,pos,?_⟩
  filter_upwards [read] with f price
  change ‖Lobby.evaluateR (chart G) (Lodge.basisR C) Q labels T μ k f -
    tour M labels μ (testP T f) univ k‖ ≤ B*Real.exp (-Tide.mildG*(theta f.sample.F)) at price
  rw [located C Q labels μ k K,Flight.in_space labels μ f M sep _ f.signs.2.1 rfl] at price
  convert price using 2
  rw [theta_value f.signs.2.2.1,Real.rpow_def_of_pos f.sample.F.positive]
  ring_nf

end YM.Integration.WilsonPositionProgramOriginalLanding
