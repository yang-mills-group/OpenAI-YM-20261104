import YM.Integration.WilsonSeparatedOriginalCaptureReplay

/-! Read the actual three originating clinics and the exact lower replay at the
three physical labels and their true cells, including nonzero motions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalCaptureAtOrigin
open Function Filter Finset Lattice Wilson RG Source Extra.Histories Push Local Marker
open MergeProof Accent Menu RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Records
open RG05Readout.Native RG05Readout.View GridApprox.Nil WilsonAllDateHarvestPropagation WilsonAllDateHarvestStability
open Bid Pressure Copper Ac Extra.Trajectories PhysicalNext.Repeat Next.Rank.Station
open WilsonAllDateHarvestObservedReplay WilsonSeparatedOriginalResidentReadout WilsonSeparatedOriginalMarkedCubic
open scoped Classical BigOperators Topology
variable {G:Gauge}{C:Family G}{n t N per:ℕ}
variable (o:Fin 3→Site (C.side n per))(E:Fin 3→Motion)(s:Fin 3→ℕ)(q:ManyStem C o n→Body)
variable (S:(i:Fin 3)→Emblems C (s i))(x:(i:Fin 3)→Palette C (s i))

def clinics (t N:ℕ)(i:Fin 3):Goods G (C.side N per):=
  clinic C per N (s i) (Launch (m:=t) s S x i N) n (o i) (E i) (q ((Mine.remap o E).symm i))

theorem registered (t N:ℕ)(i:Fin 3):
    WilsonMixedTaggedFields.columns o E s q S x t N n ((Mine.remap o E).symm i)=clinics o E s q S x t N i:=by
  unfold WilsonMixedTaggedFields.columns clinics
  rw [(headlines (N:=N) o E q).1,Mine.carried]
  rfl

/-- Physical normalized three-point data at the same actual original parent
origin. The appointed replay is selected before every healthy observation. -/
theorem original (h:C.Makes)(P:(i:Fin 3)→Sight C (s i) per)(roster:Census (Fin 3))
    (full:univ∈roster.choices)(nt:n < t)(tN:t ≤ N)(d k:ℕ)(Q fee:ℝ)
    (paid:Captured o E s q h P S x roster nt.le tN d k Q fee):
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
        (connected (((Y n).eval W:ℂ)⁻¹ • L n W)).part (modes z present univ)‖≤fee:=by
  intro A J I Y M inc opened z present
  obtain ⟨L,reg,initial,dates⟩:=WilsonSeparatedOriginalCaptureReplay.original h o E s q P S x roster nt.le tN d k Q fee paid
  refine ⟨L,reg,initial,?_⟩
  intro W clear
  have billed:=dates n le_rfl nt z (Mine.remap o E).symm.injective present W clear
  have actual:moment C z (WilsonMixedTaggedFields.columns o E s q S x t N n) (nt.le.trans tN) W=
      moment C id (clinics o E s q S x t N) (nt.le.trans tN) W:=by
    funext a;unfold WilsonSeparatedOriginalMarkedCubic.moment;congr 1;funext V;apply prod_congr rfl;intro i _
    exact congrFun (registered o E s q S x t N i) V
  rwa [actual] at billed

end YM.Integration.WilsonSeparatedOriginalCaptureAtOrigin
