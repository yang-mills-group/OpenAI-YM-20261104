import YM.RG05Readout.Records.Gust
import YM.MergeProof.South.Admit
import YM.Integration.ActualTrajectoryTransport

/-! Center the whole filed Wilson board at the earlier actual conditional law.
The authentic multi-marked regular and forced terms retain their joint bill. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalCenteredBoard
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker RG05Readout Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Records
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}(C:Family G){I:Type}[Fintype I][DecidableEq I]{B B':Census I}{N per j u:ℕ}
local notation "Y"=>C.path.rep N per

def adjustment (f:I→Goods G (C.side N per))(uN:u ≤ N)(U:Config G (C.side u per))(i:I):ℂ:=
  -actualTransport C (N:=N) (f i) uN U

lemma restricted {n:Side}(included:B'.choices⊆B.choices)(v:I→ℂ)(Z:Config G n→Poly B):
    (fun V=>narrow included (spice B v Z V))=spice B' v (fun V=>narrow included (Z V)):=by
  have placed:narrow included (Mach B v)=Mach B' v:=by
    unfold narrow;rw [feed_mach];congr 1;funext i;simp
  have silent:(narrow included (Mach B v)).part B'.quiet=0:=by rw [narrow_right];exact mute B v
  funext V;unfold spice;rw [map_mul,YM.Multi.pass_map _ _ (mute B v) silent,placed]

/-- The adjustment is computed from the same genuine upper law, once for the
specified lower configuration. Both burns take place at the same cutoff. -/
theorem reborn (f:I→Goods G (C.side N per))(included:B'.choices⊆B.choices)
    (billed:Integrable (birth B (Y N) f) (prior G _))(jn:j ≤ N)(uj:u ≤ j)(U:Config G (C.side u per)):
    let v:=adjustment C f (uj.trans jn) U
    let dressed:=birth B (Y N) (fun i V=> v i+f i V)
    Integrable dressed (prior G _) ∧ (fun W=>narrow included (gust C.path N per N dressed j jn W))=
      spice B' v (fun W=>narrow included (gust C.path N per N (birth B (Y N) f) j jn W)):=by
  intro v dressed
  have initial:dressed=spice B v (birth B (Y N) f):=(spice_entry (R:=B) (Y N) f v).symm
  have course:gust C.path N per N dressed j jn=spice B v (gust C.path N per N (birth B (Y N) f) j jn):=by
    rw [initial]
    exact Records.gale (LinearMap.mulLeft ℂ (Poly.pass (Mach B v))) jn _ billed
  exact ⟨initial ▸ spice_live v billed, by rw [course];exact restricted included v _⟩

/-- The same original Served receipt applies to all the shifted components,
including their full correlated old gas and every attached regular term. -/
theorem original (made:C.Makes)(f:I→Goods G (C.side N per))(included:B'.choices⊆B.choices)
    (billed:Integrable (birth B (Y N) f) (prior G _))(jn:j ≤ N)(uj:u ≤ j)(U:Config G (C.side u per))
    (rows:I→Three G (C.side j per))(o:I→Site (C.side j per))(w:I→ℝ)(d a:ℝ)
    (book:MenuBoard (Y j) rows (fun W=>narrow included (gust C.path N per N (birth B (Y N) f) j jn W)) o w d a):
    let v:=adjustment C f (uj.trans jn) U
    let filed:=fun W=>narrow included (gust C.path N per N (birth B (Y N) (fun i V=>v i+f i V)) j jn W)
    Served (Y j) (fun i W=>(rows i).2.1 W+v i) (fun i=>profile (Y j).activities (rows i).2.2) filed o w d a ∧
    Integrable filed (prior G _) ∧ ∀W,(filed W).part B'.quiet=(Y j).eval W ∧
      ∀i,(filed W).part (B'.fire i)=(rows i).1 W+v i*((Y j).eval W:ℂ):=by
  intro v filed
  let X:=fun W=>narrow included (gust C.path N per N (birth B (Y N) f) j jn W)
  have old:filed=spice B' v X:=(reborn C f included billed jn uj U).2
  rw [old]
  have same:spice B' v X = Accent.couple X (fun i _=>v i):=by funext W;unfold spice Accent.couple;rw [mul_comm]
  refine ⟨?_,spice_live v book.cleared,?_⟩
  · rw [same];exact book.grants.jelly
  · intro W
    have sale:=book.check (made.wilson.represents N per j jn).good.labels W
    have silent:(Mach B' v).part B'.quiet=0:=mute B' v
    constructor
    · unfold spice;rw [Poly.quiet_mul,Poly.pass_part _ silent,one_mul,sale.1]
    · intro i;unfold spice;rw [shock,Poly.pass_part _ silent,whisper _ _ silent,Accent.sing,one_mul,sale.1,sale.2 i]

end YM.Integration.WilsonSeparatedOriginalCenteredBoard
