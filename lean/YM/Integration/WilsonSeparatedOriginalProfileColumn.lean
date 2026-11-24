import YM.Integration.WilsonSeparatedOriginalProfileReplay
import YM.Integration.WilsonSeparatedOriginalReplicaScanner

/-! The actual pre-elected lower replay for every emitted product test. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedOriginalProfileColumn
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Extra.Histories Push Local Marker
open MergeProof Accent Menu RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Records
open RG05Readout.Native RG05Readout.View GridApprox.Nil WilsonAllDateHarvestPropagation WilsonAllDateHarvestStability
open Bid Pressure Copper Ac Extra.Trajectories PhysicalNext.Repeat Next.Rank.Station Extraction PhysicalNext.Repeat.Legato
open WilsonAllDateHarvestObservedReplay WilsonSeparatedOriginalResidentReadout WilsonSeparatedOriginalMarkedCubic
open WilsonSeparatedOriginalCaptureAtOrigin RG05Readout.Nuclear RG05Readout.Pulse RG05Readout.Flatten
open WilsonSeparatedOriginalReplicaScanner WilsonSeparatedOriginalProfileReplay
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G){n t N per:ℕ}
variable (o:Fin 3→Site (R.family.side n per))(s:Fin 3→ℕ)
variable (S:(i:Fin 3)→Emblems R.family (s i))(x:(i:Fin 3)→Palette R.family (s i))
variable (P:(i:Fin 3)→Sight R.family (s i) per)(roster:Census (Fin 3))
    (full:univ∈roster.choices)(nt:n<t)(tN:t≤N)

def Posted (fee:ℝ)(f:Fin 3→Body)(result:Config G (R.family.side n per)→ℂ):Prop:=
  let E:=fun _:Fin 3=>(1,false)
  let A:=Mine.tree o E
  let J:=Mine.ward o E roster
  let q:=fun w:ManyStem R.family o n=>f w.val.1
  let Y:=R.family.path.rep N per
  let M:=imprint R.makes A (headings o E q) (plants (m:=t) s P S x) t tN
  let inc:=WilsonMixedTaggedSeparatedBoard.admitted o E roster nt.le (le_refl t)
  let opened:=WilsonAllDateHarvestEndpointOpening.opening inc (shadow A s (headings o E q) t)
  let z:=fun v:Fin 3=>(Mine.remap o E).symm v
  let present:=WilsonSeparatedOriginalCaptureReplay.placed o E roster full
  ∃ L:∀i,Config G (R.family.side i per) → Poly (J i),Replay A s (le_refl n) t L N ∧
    L t=(fun W=>opened (density (Y t) M (fun _ _=>0) (fun _ _=>0) W)) ∧
    result=(fun W=>(connected (((Y n).eval W:ℂ)⁻¹ • L n W)).part (modes z present univ)) ∧
    ∀W,flags (Y n).p.threshold W=∅ →
      ‖sample R s (fun i=>Launch (m:=t) s S x i N) o (nt.le.trans tN) (nt.trans_le tN) W (joint univ f)-result W‖≤fee

theorem received {fee:ℝ}{f:Fin 3→Body}
    (paid:Filed o (fun _=>(1,false)) s (fun w=>f w.val.1) S x R.makes P roster full nt tN fee):
    ∃A,Posted R o s S x P roster full nt tN fee f A:=by
  obtain ⟨L,path,top,bound⟩:=paid
  refine ⟨_,L,path,top,rfl,?_⟩
  intro W healthy
  rw [WilsonSeparatedOriginalReplicaScanner.clinic]
  exact bound W healthy

theorem estimate {fee:ℝ}{f:Fin 3→Body}{A:Config G (R.family.side n per)→ℂ}
    (paid:Posted R o s S x P roster full nt tN fee f A)(W:Config G (R.family.side n per))
    (clean:flags (R.family.path.rep N per n).p.threshold W=∅):
    ‖sample R s (fun i=>Launch (m:=t) s S x i N) o (nt.le.trans tN) (nt.trans_le tN) W (joint univ f)-A W‖≤fee:=by
  obtain ⟨_,_,_,_,bound⟩:=paid;exact bound W clean

end YM.Integration.WilsonSeparatedOriginalProfileColumn
