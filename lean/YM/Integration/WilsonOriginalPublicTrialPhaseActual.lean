import YM.Integration.WilsonOriginalPublicTrialPhaseLocated
import YM.Integration.WilsonOriginalPublicTrialPhaseTileSites
import YM.Integration.WilsonOriginalPublicTrialPhaseLanding
import YM.Integration.WilsonOriginalPublicTrialPhaseCopiedRide

/-! Every complete marked tile, including all of its original hard records,
passes through the first true Wilson edge on its ordinary finite density. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseActual
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells
open Push Local Planned.GuardedAtom Guard MergeProof MergeProof.Accent Marker
open MergeProof.Ribbons MergeProof.Ribbons.ManyCopies MergeProof.Ribbon MergeProof.Float
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign OPE.Therm Push.GridApprox
open RG05Readout RG05Readout.Address RG05Readout.Many
open WilsonOriginalPublicTrialPhaseCoFiled (copies)
open WilsonOriginalPublicTrialPhaseFiling (reserve)
open WilsonOriginalPublicTrialPhaseTiles (motion)
open WilsonOriginalPublicTrialPhaseRate (wage)
open WilsonOriginalPublicTrialPhaseLanding (first)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){N j m per:ℕ}{I:Type}[Fintype I][DecidableEq I]
local notation "C" => R.family
local notation "H" => (C).path
local notation "P" => (H).rep N per (m+1)
local notation "Q" => (H).rep N per m
local notation "O" => (H).levels.clock.op m per
local notation "L" => (C).S.block m

set_option maxHeartbeats 1150000 in
theorem original (stock:RG05Readout.Many.Storage (C) R.doors)(hm:m<N)(jm : j ≤ m)
    (d:I→ℕ)(z:I→Site ((C).side (m+1) per))(v:∀i,(C).label (d i))
    (q:∀i,Coefficient ((C).labels.level (d i)) ((C).side (m+1) per))
    (writes:∀i U,(q i).density (z i) ((C).localSection (d i)) (P) U=
      ((P).eval U:ℂ)*WilsonPositionProgramBlockedTrialAddBack.uncut R (d i) N per (m+1) (z i) (v i) U)
    (dom₀:∀i,Dominated (q i).forced)(ψ:I→MergeProof.Response G ((C).side (m+1) per))
    (won:∀i,Attainment (P).p (z i) (ψ i) (reserve R (N:=N) (d i) (z i) (v i)))
    (hook:∀i,profile (P).activities (q i).forced=MergeProof.hook (P).activities (P).p.threshold (ψ i))
    (Y:I→Three G ((C).side m per))(price:I→ℝ)
    (step:∀i,Ride (O) (z i) ((O).ratio.parent (z i)) (R.doors N per m hm)
      (((L).val:ℂ)^(d i)) (invoice (q i) (z i) ((C).localSection (d i)) (P)) (Y i) (price i))
    (opening:WilsonOriginalPublicTrialPhaseRate.volume (P).p.B*(H).levels.clock.forcedAllowance (m+1)≤Real.log 2/2)
    (exp₀:0≤(P).p.supportExponent-3)
    (room:Fintype.card I*Fintype.card Signed≤apron (H).levels m):
    let T:=tilesAt (C).S per (jm.trans m.le_succ)
    let U:=tilesAt (C).S per jm
    let F:=fun i:T.Cell×I=>T.copy i.1 (WilsonPositionProgramBlockedTrialAddBack.uncut R
      (d i.2) N per (m+1) (z i.2) (v i.2))
    let o:=fun i:T.Cell×I=>T.copyMap i.1 (z i.2)
    let w:=fun i=>wage (P).p.B (Fintype.card I*Fintype.card Signed) (reserve R (N:=N) (d i) (z i) (v i))
    let w':=fun i=>Bandage.renal (H).levels m*first (w i) (price i)
    ∀ (π:∀b,(P).activities.Moves (motion T b).1 (T.translateBy b))
      (μ:∀b,(Q).activities.Moves (motion U b).1 (U.translateBy b)),
      let H₀:=fun i=>invoice (q i) (z i) ((C).localSection (d i)) (P)
      let H₁:=copies (Q) 0 (motion U) U.translateBy μ Y
      (∀i,0<w' i) ∧
        MenuBoard (P) (copies (P) 0 (motion T) T.translateBy π H₀)
          (birth (Names T.Cell I) (P) F) o (fun i=>w i.2) ((P).p.supportExponent-3) 1 ∧
        MenuBoard (Q) (fun i=>(((L).val:ℂ)^(d i.2))⁻¹ • H₁ i)
          ((O).push (P).beta (birth (Names T.Cell I) (P) F))
          ((O).ratio.parent ∘ o) (fun i=>w' i.2) ((H).levels.budget m).supportExponent 1:=by
  intro T U F o w w' π μ H₀ H₁
  obtain ⟨_,pos,upper⟩:=WilsonOriginalPublicTrialPhasePaidBoard.original R hm T d z v q writes dom₀ ψ won hook π opening exp₀
  have rides:=WilsonOriginalPublicTrialPhaseCopiedRide.original R stock hm jm z d price H₀ Y step π μ
  have sites:=WilsonOriginalPublicTrialPhaseTileSites.original R jm z
  have one (i:T.Cell×I):1≤‖((L).val:ℂ)^(d i.2)‖:=by
    rw [norm_pow,Complex.norm_natCast]
    exact one_le_pow₀ (by exact_mod_cast (L).property)
  let Z:=copies (P) 0 (motion T) T.translateBy π H₀
  obtain ⟨live,down⟩:=WilsonOriginalPublicTrialPhaseLanding.original R stock hm o
    (fun i:T.Cell×I=>w i.2) (fun i=>price i.2) (fun i=>((L).val:ℂ)^d i.2)
    Z H₁ (birth (Names T.Cell I) (P) F) (fun i=>pos i.2) one upper rides
    (fun x=>(sites.1 x).trans room) (fun x=>(sites.2 x).trans room)
  refine ⟨fun i=>live (0,i),upper,?_⟩
  exact down

end YM.Integration.WilsonOriginalPublicTrialPhaseActual
end
