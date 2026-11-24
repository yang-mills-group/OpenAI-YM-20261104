import YM.Integration.WilsonOriginalPublicTrialPhaseCenteredBirth
import YM.Integration.WilsonOriginalPublicTrialPhaseTileInvoice

/-! At the original flat receiver all oriented replica centers are copies of the same real-history reading. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseReplicaCenters
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof MergeProof.Accent MergeProof.Menu Marker Ac
open GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open RG05Readout RG05Readout.Address RG05Readout.Many RG05Readout.Pantry
open OPE.Therm Push.GridApprox PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open Cells WilsonOriginalPublicTrialPhaseCenterMenu
open scoped Classical BigOperators ContDiff
open WilsonOriginalPublicTrialPhaseTiles
variable {G:Gauge}(R:Run G){j u K N per:ℕ}
local notation "C" => R.family
local notation "A" => (C).path
local notation "P" => (A).rep N per
local notation "T" => tilesAt (C).S per

theorem spin {n:Side}(t:Tiling n)(v:t.Cell)(f:Config G n→ℂ):
    t.copy v f=stepUp (motion t v) (t.translateBy v) f:=by
  funext U
  simp [Tiling.copy,stepUp,motion,Motion.scalar]

theorem transmitted (uk:u≤K)(M:Config G ((C).side K per)→ℂ)(pay:Integrable M (prior G _))
    (ju:j≤u)(v:Site ((C).side j per)):
    gust (A) N per K (((T) (ju.trans uk)).copy v M) u uk=
      ((T) ju).copy v (gust (A) N per K M u uk):=by
  revert ju
  induction uk using Nat.decreasingInduction with
  | self=> intro ju;rw [gust_base,gust_base]
  | of_succ m mk ih=>
    intro jm
    let t:=(T) (jm.trans m.le_succ)
    let b:=(T) jm
    let o:=b.translateBy v
    let s:=motion b v
    let f:=gust (A) N per K M (m+1) mk
    have id:t.translateBy v=((A).levels.clock.op m per).ratio.embed o:=by
      change ((T) (jm.trans m.le_succ)).translateBy v=((A).levels.clock.op m per).ratio.embed (((T) jm).translateBy v)
      rw [tile_translate,tile_translate]
      exact (anchor_next (C).S per jm v).symm
    rw [gust_step (A) N per K _ mk,gust_step (A) N per K M mk,ih (jm.trans m.le_succ)]
    rw [spin,spin,id]
    exact (show ((A).levels.clock.op m per).push ((A).β N per (m+1))
        (stepUp s (((A).levels.clock.op m per).ratio.embed o) f)=stepUp s o _ from
      by simpa only [blast,pow_zero,one_smul] using
        unison s (A) m N per 0 o f (gust_live (A) N per K M pay mk))

theorem original (uk:u≤K)(ju:j≤u)(live:K≤N)
    (M:Config G ((C).side K per)→ℂ)(v:Site ((C).side j per))
    (pay:Integrable (fun U=>(((P) K).eval U:ℂ)*M U) (prior G _)):
    gust (A) N per K (fun U=>(((P) K).eval U:ℂ)*((T) (ju.trans uk)).copy v M U) u uk=
      ((T) ju).copy v (gust (A) N per K (fun U=>(((P) K).eval U:ℂ)*M U) u uk):=by
  let t:= (T) (ju.trans uk)
  let b:=(T) ju
  let s:=motion t v
  let d:=fun U=>(((P) K).eval U:ℂ)*M U
  have initial:(fun U=>(((P) K).eval U:ℂ)*t.copy v M U)=stepUp s (t.translateBy v) d:=by
    obtain ⟨moves⟩:=(R.makes.wilson.represents N per K live).good.labels.moves s.1 (t.translateBy v)
    funext U
    rw [spin]
    change _=Motion.scalar s (((((P) K).eval (pull s.1 (t.translateBy v) U):ℂ))*M _)
    have quiet:((P) K).eval (pull s.1 (t.translateBy v) U)=((P) K).eval U:=Push.Local.eval_pull moves U
    rw [quiet,Motion.scalar_mul,Motion.scalar_real]
    rfl
  change gust (A) N per K _ u uk=b.copy v _
  rw [initial,←spin]
  exact transmitted R uk d pay ju v

theorem flat (uk:u≤K)(ju:j≤u)(live:K≤N)
    (M:Config G ((C).side K per)→ℂ)(v:Site ((C).side j per))
    (pay:Integrable (fun U=>(((P) K).eval U:ℂ)*M U) (prior G _)):
    gust (A) N per K (fun U=>(((P) K).eval U:ℂ)*((T) (ju.trans uk)).copy v M U) u uk 1/
        (((P) u).eval 1:ℂ)=
      Motion.scalar (motion ((T) ju) v) (gust (A) N per K (fun U=>(((P) K).eval U:ℂ)*M U) u uk 1/
        (((P) u).eval 1:ℂ)):=by
  rw [original R uk ju live M v pay,spin]
  unfold stepUp
  rw [ProjectorNext.Equivariance.pull_constant]
  unfold Motion.scalar
  split <;> simp

end YM.Integration.WilsonOriginalPublicTrialPhaseReplicaCenters
end
