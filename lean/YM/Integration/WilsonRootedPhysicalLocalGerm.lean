import YM.Integration.WilsonRootedPhysicalTaylorPeriod
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hem
import YM.Extra.WILSON_STARTUP.Face

/-! Exact localization of the physical retained germ, including its genuine rough-field switches. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedPhysicalLocalGerm
open Function Filter Finset Set Lattice Wilson RG RG.Shoot Pressure
open Push Push.AbsoluteSums Push.AbsoluteSums.Animals Gas Ursell Trees Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes PhysicalNext PhysicalNext.Repeat Legato
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Blaze Blaze.March Captain
open Opera Height Beam Song Geo Greenbelt Next.Scheduling Extra.Iteration UVNext
open PriceCompiler Org Input Supply Pressure.Testing Time Roost Match Refrain WilsonStartup
open RG01Estimate RG01Estimate.CensusStep WilsonLimitConstruction.FundedCensusVacuum
open WilsonVacuumPreResetCatalogue WilsonRootedPhysicalHousing
open scoped Topology BigOperators Classical

variable {G : Gauge} {n:Side}

def paste (A : Support n) (U V:Config G n) : Config G n:=fun e=>if e.1∈A then U e else V e

def tangent (A : Support n) (u : Directions G n): Directions G n:=fun e=>if e.1∈A then u e else 0

lemma inside (x:Site n) (q:ℕ) (A:Support n) (ha:A⊆neighbors q x) :
    inspected A⊆neighbors (q+4) x:=by
  intro y hy
  rcases Finset.mem_union.mp hy with h|h
  · exact (neighbors_mem ..).2 (((neighbors_mem ..).1 (ha h)).trans (by omega))
  rcases Finset.mem_biUnion.mp h with ⟨p,_,hp⟩
  by_cases dis : Disjoint A (touched p)
  · simp [dis] at hp
  have yp:y∈touched p:=by simpa only [if_neg dis] using hp
  obtain ⟨v,hv,hv'⟩:=Finset.not_disjoint_iff.mp dis
  have a:= (neighbors_mem ..).1 (ha hv)
  have b:= WilsonStartup.visit_near p hv'
  have c : separation p.1 y≤2:=by rw [separation_comm];exact WilsonStartup.visit_near p yp
  apply (neighbors_mem ..).2
  exact (separation_triangle x v y).trans (Nat.add_le_add a ((separation_triangle v p.1 y).trans (Nat.add_le_add b c)))

/-- The masked root is local on the actual plaquette inspections, on every field. -/
theorem switches {Z:Listing G n} {q:ℕ} {f:ℕ→ Config G n→ℝ} (C:Abacus.Rack Z q f)
    (B:BudgetPoint) {c:ℝ} (rows:Meadow.Budget B Z.reg f c) (x:Site n) :
    LocalOn (neighbors (q+4) x) (C.maskedEntry B x):=by
  obtain ⟨_,_,row⟩:=rows
  intro U V agree
  apply Finset.sum_congr rfl
  intro i hi
  by_cases active:C.seat i x=0
  · rw [active,zero_mul,zero_mul]
  apply congrArg (fun t:ℝ=>C.seat i x*t)
  have placed:=C.priced i hi x active
  have localMask:=CouplingShape.stencil_reads (Z.reg i).support (row i).1.sites B.threshold
  exact (UsesFinal.allReads _ _ _ localMask) U V (agrees_mono agree (inside x q _ placed))

/-- The original unmasked polygon and all its ordered left jets live on the one declared support. -/
theorem directions {Z:Listing G n} {q:ℕ} {f:ℕ→ Config G n→ℝ} (C:Abacus.Rack Z q f)
    (B:BudgetPoint) {c:ℝ} (rows:Meadow.Budget B Z.reg f c) (x:Site n) (U V:Config G n)
    (l:List (Directions G n)) :
    leftDerivs (C.polygon x) l U=leftDerivs (C.polygon x) (l.map (tangent (neighbors q x)))
      (paste (neighbors q x) U V) :=
  March.stays (C.plating B rows x).sites l _ (fun _ _ _ he=>if_pos he) U _
    (fun _ he _=>Eq.symm (if_pos he))

variable (R : Run G)

/-- A housed original physical regular roster has its actual local Taylor germ even at arbitrarily
rough exteriors. The mask comparison uses the complete plaquette read, on all fields. -/
theorem original (simple:G.Simple) (r:ℕ) :
  ∀ᶠm:ℕ in atTop,∀N per,∀hm:m<N,let S:=station R N per m hm
  let B:=R.alloy.B.a.budget m
  ∀D t,let C:=WilsonRootedPhysicalHousing.rack R S r D t
  let q:=WilsonRootedPhysicalHousing.radius B D
  ∀x, B.Regular (neighbors q x) (C.polygon x) ∧
  (∀U V:Config G (R.family.side m per),∀l:List (Directions G (R.family.side m per)),
    leftDerivs (C.polygon x) l U=leftDerivs (C.polygon x) (l.map (tangent (neighbors q x))) (paste (neighbors q x) U V)) ∧
  ∀U V:Config G (R.family.side m per),C.maskedEntry B x U=C.maskedEntry B x (paste (neighbors (q+4) x) U V):=by
  filter_upwards [WilsonLimitConstruction.FundedCensusVacuum.paid R simple r] with m income N per hm S B D t C q x
  let H:=S.guide
  let Y:=ledger R.kit H
  let π:=WilsonRootedPhysicalHousing.spatial R S t D
  let g:=portion R S r π
  have h:=income N per hm
  have rows : Meadow.Budget B Y.reg g (Opera.earlyFee (p:=R.kit.expense) R.alloy.B N m
      (R.family.path.rep N per (m+1)).beta):=by
    change Meadow.Budget _ _ (portion R S r π) _
    rw [funext (WilsonVacuumPreResetCatalogue.selected R S r π)]
    convert Acquire.budget_cut (fun i=>i∈Caddy.entries S.guide π) (Abacus.charted B h.low) using 1
    funext i
    by_cases ha:i∈Caddy.entries S.guide π <;> simp [ha]
    rfl
  refine ⟨C.plating B rows x,directions C B rows x,?_⟩
  intro U V
  exact switches C B rows x U _ (fun _ he _=> Eq.symm (if_pos he))

end YM.Integration.WilsonRootedPhysicalLocalGerm
