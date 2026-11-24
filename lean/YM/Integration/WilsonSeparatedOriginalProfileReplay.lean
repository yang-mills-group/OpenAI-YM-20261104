import YM.Integration.WilsonSeparatedOriginalCaptureAtOrigin
import YM.Integration.WilsonMixedTaggedPhysicalTest
import YM.RG05Readout.Pulse.Chills

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalProfileReplay
open Function Filter Finset Lattice Wilson RG Source Extra.Histories Push Local Marker
open MergeProof Accent Menu RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Records
open RG05Readout.Native RG05Readout.View GridApprox.Nil WilsonAllDateHarvestPropagation WilsonAllDateHarvestStability
open Bid Pressure Copper Ac Extra.Trajectories PhysicalNext.Repeat Next.Rank.Station
open WilsonAllDateHarvestObservedReplay WilsonSeparatedOriginalResidentReadout WilsonSeparatedOriginalMarkedCubic
open WilsonSeparatedOriginalCaptureAtOrigin RG05Readout.Nuclear RG05Readout.Pulse RG05Readout.Flatten
open scoped Classical BigOperators Topology
variable {G:Gauge}{C:Family G}{n t N per:ℕ}
variable (o:Fin 3→Site (C.side n per))(E:Fin 3→Motion)(s:Fin 3→ℕ)(q:ManyStem C o n→Body)
variable (S:(i:Fin 3)→Emblems C (s i))(x:(i:Fin 3)→Palette C (s i))

def Filed (h:C.Makes)(P:(i:Fin 3)→Sight C (s i) per)(roster:Census (Fin 3))
    (full:univ∈roster.choices)(nt:n < t)(tN:t ≤ N)(fee:ℝ) : Prop :=
    let A:=Mine.tree o E
    let J:=Mine.ward o E roster
    let I:=headings o E q
    let Y:=C.path.rep N per
    let M:=imprint h A I (plants (m:=t) s P S x) t tN
    let inc:=WilsonMixedTaggedSeparatedBoard.admitted o E roster nt.le (le_refl t)
    let opened:=WilsonAllDateHarvestEndpointOpening.opening inc (shadow A s I t)
    let z:=fun v:Fin 3=>(Mine.remap o E).symm v
    let present:=WilsonSeparatedOriginalCaptureReplay.placed o E roster full
    ∃ L:∀i,Config G (C.side i per) → Poly (J i),Replay A s (le_refl n) t L N ∧
      L t=(fun W=>opened (density (Y t) M (fun _ _=>0) (fun _ _=>0) W)) ∧
      ∀W:Config G (C.side n per),flags (Y n).p.threshold W=∅ →
      ‖cubic (moment C id (clinics o E s q S x t N) (nt.le.trans tN) W)-
        (connected (((Y n).eval W:ℂ)⁻¹ • L n W)).part (modes z present univ)‖≤fee

/-- All weights and the entire original wave are retained. Each admitted
three-body product comes with a measured physical replay at its own origin. -/
theorem purchased (h:C.Makes)(P:(i:Fin 3)→Sight C (s i) per)(roster:Census (Fin 3))
    (full:univ∈roster.choices)(nt:n < t)(tN:t ≤ N)(d k:ℕ)(Q error:ℝ)
    {r η X:ℝ}(rp:0 < r)(room:r ≤ C.S.a n)(sep:0 < η)(small:η ≤ 1)
    (Ψ:Wave (Fin 3))(rank:ℕ)(grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3) < rank+1)
    (scatter:Scattering Ψ η)(xp:0 ≤ X)(cap:Tall Ψ (rank+1) 1 X)
    (submitted:∀f:Fin 3→Body,(∀i,Tall (f i) (s i+2) 1 1) → buy C n per o (r*η/2) f →
      Captured o (fun _=>(1,false)) s (fun z=>f z.val.1) h P S x roster nt.le tN d k Q error):
    let top:=nt.le.trans tN
    let admit:=fun f:Fin 3→Body=>buy C n per o (r*η/2) f ∧
      Filed o (fun _=>(1,false)) s (fun z=>f z.val.1) S x h P roster full nt tN error
    ∃ F:E4→Wave (Fin 3),Bouquet s Native.box admit F (earn s C n rank η r*X) ∧
      ∀(τ:E4)(e:ℕ),e ≤ ∑i,s i → ∀w:Fin 3→Site (C.S.toDepth top per).count,
        pie (F τ) (cropX Ψ o r τ) e (placeR (C.S.toDepth top per) ∘ w):=by
  classical
  intro top admit
  obtain ⟨F,rent,points⟩:=regent s (C:=C) (p:=per) top o r η Ψ rp room sep small grade scatter xp cap
  refine ⟨F,WilsonMixedTaggedPhysicalTest.relabel ?_ rent,points⟩
  intro f size enrolled
  exact ⟨enrolled,WilsonSeparatedOriginalCaptureAtOrigin.original o (fun _=>(1,false)) s
    (fun z=>f z.val.1) S x h P roster full nt tN d k Q error (submitted f size enrolled)⟩

end YM.Integration.WilsonSeparatedOriginalProfileReplay
