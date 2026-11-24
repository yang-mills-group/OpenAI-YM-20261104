import YM.Integration.OriginalMarkedBirthStencil

/-! The genuine submitted normalized Q has only the original finite row
indices. Its physical coupling is already inside each token. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.OriginalMarkedBirthRows
open Function Finset Lattice Wilson RG Marker FVA1 PhysicalNext.Repeat.Legato
open LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Pert.Asymptotics
open scoped Classical BigOperators

variable {G : Gauge} {B : MS.Local.Physical.Deck G} {V : Type} [Fintype V] [DecidableEq V]
  (R : Run G) (hG : G.Simple) (u : V→MS.Rake.Label B) (J : Request V)
  (A : NumericSchedule R.family J) (z : LocalFormal.Datum R.family (Stock.census V))
  (Q : MS.Land.Prescription B) (o : V→Site (R.family.side (z.level+1) z.period))
  (μ : ℝ) (orders : V→ℕ)
local notation "D" => ActualOriginalQPointSetup.pointDatum R J z.period (z.level+1) o
local notation "M" => ActualOriginalQInitialInput.packets R hG u J A z Q o μ orders
local notation "clock" => μ-R.family.S.scale z.cutoff
local notation "g" => regulatorRun R.family z.cutoff z.period (z.level+1)
local notation "count" => ActualOriginalQPackets.packetCount (R:=R) u

theorem absent (i : ℕ) (hi : count ≤ i) : (M).packet i=none := by
  let P := ActualOriginalQPackets.packets Q (D) u (clock) orders z.cutoff
  have bare : P.packet i=none := by
    unfold P ActualOriginalQPackets.packets
    exact MarkedPackets.ofFin_absent _ _ _ _ _ _ i hi
  change ((ActualPacketCouplingFreeze.freeze P (g)).packet i).map _=none
  simp only [ActualPacketCouplingFreeze.freeze_packet,bare,Option.map_none]
  rfl

theorem frozenPower (i : ℕ) : (M).power i=0 := rfl

theorem field (x : TestSpace (ActualOriginalQPointSetup.request R u J).tests)
    (v : ℝ) (U : Config G (R.family.side (z.level+1) z.period)) (i : ℕ) :
    (M).term x v U i=(M).term x 1 U i := by
  simp only [MarkedPackets.term,frozenPower,zpow_zero]

def active : Finset ℕ := (Finset.range count).filter fun i=>((M).packet i).isSome
local notation "E" => active R hG u J A z Q o μ orders

theorem present (i : ℕ) : i∈(E) ↔ ((M).packet i).isSome := by
  rw [active,Finset.mem_filter]
  refine ⟨And.right,fun h=>⟨Finset.mem_range.mpr ?_,h⟩⟩
  by_contra! tooLate
  simp [absent R hG u J A z Q o μ orders i tooLate] at h

end YM.Integration.OriginalMarkedBirthRows
end
