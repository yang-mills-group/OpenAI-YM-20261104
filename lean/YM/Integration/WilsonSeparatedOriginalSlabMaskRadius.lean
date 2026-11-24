import YM.Integration.WilsonReportHarvestSlabShiftSingle

/-! Halving the actual original mark radii restores the manuscript's half-unit budget after a bounded simultaneous shift. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabMaskRadius
open MeasureTheory Finset Lattice Wilson Labels RG Source Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V:Type}{I A:Type*}[DecidableEq V]{S:Census V}

theorem cheaper {w w':V→ℝ}(h:∀i,0≤w' i)(le:∀i,w' i≤w i){s:I→Support n}{F:I→A→Poly S}{B:ℕ}{d t:ℝ}
    (old:Towed w s F B d t):Towed w' s F B d t:=by
  obtain ⟨c,hs,hit,rows⟩:=old
  refine ⟨c,hs,hit,fun i=>?_⟩
  obtain ⟨a,ap,major,cost⟩:=rows i
  refine ⟨a,ap,major,le_trans (Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_right ?_ (ap j))) cost⟩
  exact Finset.prod_le_prod (fun k _=>h k) (fun k _=>le k)

theorem thin [Fintype V] {X:Rep G n}{P:V→Three G n}{F:Config G n→Poly S}{o:V→Site n}{w:V→ℝ}{t e c:ℝ}
    (hp:∀i,0≤w i)(original:Alcove X P F o w t e c):Alcove X P F o (fun i=>w i/2) t e (c/2):=by
  obtain ⟨H,K,ψ,ν,hH,hK,hB,hF,hG,born,quiet,one,paper⟩:=original.chamber
  have lp(i:V):0≤w i/2:=div_nonneg (hp i) (by norm_num)
  have small(i:V):w i/2≤w i:=by linarith [hp i]
  refine ⟨original.clef,original.value,original.tally,original.price,H,K,ψ,ν,cheaper lp small hH,cheaper lp small hK,hB,hF,?_,?_,quiet,one,paper⟩
  · refine ⟨hG.yes,hG.tracks,fun i=>?_⟩
    obtain ⟨a,profile,cost⟩:=hG.fee i
    refine ⟨a,profile,(Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (small i) (profile j).1) (Real.exp_nonneg _))).trans cost⟩
  · intro i
    specialize born i
    nlinarith
end YM.Integration.WilsonSeparatedOriginalSlabMaskRadius
