import YM.Integration.WilsonAllDateHarvestObservedReplay
import YM.Integration.WilsonAllDateHarvestCenteredLedger
import YM.RG05Readout.Records.Chains

/-! The lower physical H and K estimates apply to the complete earlier-centered
three-source cutoff birth, including its vacuum, singleton and rough factors. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestCenteredReplay
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker RG05Readout Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Records
open WilsonAllDateHarvestObservedReplay WilsonAllDateHarvestStability WilsonAllDateHarvestPropagation
open WilsonSeparatedOriginalCenteredBoard
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{n t N per d k:ℕ}{Q fee:ℝ}

theorem original (o:Fin 3→Site (C.side n per)) (E:Fin 3→Motion) (s:Fin 3→ℕ)
    (q:ManyStem C o n→Body)(made:C.Makes)(P:(j:Fin 3)→Sight C (s j) per)
    (S:(j:Fin 3)→Emblems C (s j))(x:(j:Fin 3)→Palette C (s j))(roster:Census (Fin 3))
    (nt:n ≤ t)(tN:t ≤ N)(paid:Captured o E s q made P S x roster nt tN d k Q fee):
    let A:=Mine.tree o E
    let J:=Mine.ward o E roster
    let Y:=C.path.rep N per
    let I:=headings o E q
    let rows:=fun i (iN:i ≤ N)=>imprint made A I (plants (m:=t) s P S x) i iN
    let f:=WilsonMixedTaggedFields.columns o E s q S x t N
    let full:=fun i (iN:i ≤ N)=>gust C.path N per N (birth (J i) (Y N) (f i)) i iN
    let inc:=WilsonMixedTaggedSeparatedBoard.admitted o E roster nt (le_refl t)
    let openField:=WilsonAllDateHarvestEndpointOpening.opening inc (shadow A s I t)
    ∃ L:∀i,Config G (C.side i per)→Poly (J i),Replay A s (le_refl n) t L N ∧
      L t=(fun U=>openField (density (Y t) (rows t tN) (fun _ _=>0) (fun _ _=>0) U)) ∧
      ∀i,n ≤ i→∀it:i ≤ t,
        let α:=if i=t then (C.path.levels.budget i).supportExponent-4 else (C.path.levels.budget i).supportExponent
        let w:=fun _:ManyStem C o i=>RG05Readout.Many.envelope C t d k Q i
        ∃(B:Ledger (Y i) (rows i (it.trans tN)) (L i) (A.supportX i) w α)
          (Z:Ledger (Y i) (rows i (it.trans tN)) (full i (it.trans tN)) (A.supportX i) w α),
        Towed (fun _:ManyStem C o i=>(1:ℝ)) id (fun b V=>Z.H b V-B.H b V) (Y i).p.B α fee ∧
        Towed (fun _:ManyStem C o i=>(1:ℝ)) Prod.fst (fun b V=>Z.K b V-B.K b V) (Y i).p.B α fee ∧
        ∀u,∀ui:u ≤ i,∀U:Config G (C.side u per),
          let v:=adjustment C (f i) (ui.trans (it.trans tN)) U
          let centered:=birth (J i) (Y N) (fun j V=>v j+f i j V)
          let simple:=fun j V=>(rows i (it.trans tN) j).2.1 V+v j
          let rough:=fun j=>profile (Y i).activities (rows i (it.trans tN) j).2.2
          Integrable centered (prior G _) ∧
          gust C.path N per N centered i (it.trans tN)=restore (Y i) simple rough Z.H Z.K ∧
          spice (J i) v (L i)=restore (Y i) simple rough B.H B.K := by
  intro A J Y I rows f full inc openField
  obtain ⟨L,run,top,entries⟩:=paid
  refine ⟨L,run,top,?_⟩
  intro i ni it α w
  obtain ⟨B,Z,reg,hard⟩:=entries i ni it
  refine ⟨B,Z,reg,hard,?_⟩
  intro u ui U
  exact WilsonAllDateHarvestCenteredLedger.original C made (f i) (fun _=>RG05Readout.Records.clinic_cut ..)
    (it.trans tN) ui U (rows i (it.trans tN)) B Z

end YM.Integration.WilsonAllDateHarvestCenteredReplay
