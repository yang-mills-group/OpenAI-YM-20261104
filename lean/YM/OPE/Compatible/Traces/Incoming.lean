import YM.OPE.Compatible.Traces.Passage
/-! Incoming side of event. Can take all slots on the old Lights, and invoke once only.The geometry facts don't mention productions. Supports unsized arrays of copies common bill. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open Push Marker Local Extra.Histories Extra.Trajectories MeasureTheory Extra.Multi
open scoped Topology Classical
variable {G:Gauge} {C:Family G}(A:Allot C){V I J Z :Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
    [Fintype J][DecidableEq J] [Fintype Z][DecidableEq Z](P:Ensemble V)
variable {N p i b H l:ℕ}
namespace Lights
variable (F:Fibers (I⊕Z) J)(o:I→Track C.path V p) (o':J→Track C.path V p)
-- identity blanks before grouping. born's twig should be blank but not required.
def tabs (F:Fibers (I⊕Z) J)(o':J→Track C.path V p) (i:ℕ)(z:Z):= o' (F.bunch (.inr z)) i
def roots (F:Fibers (I⊕Z) J)(o:I→Track C.path V p)(o':J→Track C.path V p)(i:ℕ)(x:I⊕Z):=x.elim (fun a=>o a i) (tabs F o' i)
structure Incoming (A:Allot C) (F:Fibers (I⊕Z) J)(o:I→Track C.path V p)(o':J→Track C.path V p)(i H l:ℕ): Prop where
    twig j : roots F o o' i (F.twig j) = o' j i
    before : Occupancy (pegs V I o (i+1)) (A.r i)
    after : Occupancy (pegs V I o i) (A.r i)
    allIn : Occupancy (fun x: V×(I⊕Z)=> roots F o o' i x.2 x.1) (A.r i)
    small : ∀ x:I⊕Z, ∀ v:V,coverNumber (bins C i).B ({o' (F.bunch x) i v, roots F o o' i x v}: Support _) ≤ l
    sizes : Fintype.card (I⊕Z) ≤ H
    sizeP : 0<H
variable {A P} {E:Track C.path V p} {o} {k:I→ℕ} (L:Lights A P N p k (i+1) b E o)
    (χ:Guard (Names V I))(χ':Guard (Names V J))
variable {Y:Config G (C.S.side (i+1) p)→Marker.Poly (Names V I)}
variable {F o'} (G':Incoming A F o o' i H l)
include G'
lemma LitUp.inlet (h:L.LitUp χ Y)(hA:C.Makes)(hk:∀ a,k a≤ i)(hn:i<N)(hm:C.ref 0 < i)(hC: (C.path.levels.clock.op i p).ratio.embed ∘ E i= E (i+1))
    (hp:∀ j x,x≠P.v → o' j i x = affine (P.move x).1 (E i x) (o' j i P.v))
    (ht:∀ j,χ'.safe j→χ.safe (assembly F j)):
    let T:=grouped C.path (renal C.path.levels) H l i (Sum.elim L.asks 1) F
    let Xo a:=(L a).X i
    let Z:=reunion F ∘ (C.path.levels.clock.op i p).push (C.path.rep N p (i+1)).beta Y
    ∃ U:J→Stem V G (C.S.side i p),(∀ j,(U j).home=o' j i)∧
       Integrable Z (prior G _) ∧ Owned χ' (C.path.rep N p i) (E i) P U T ((C.path.levels.budget i).supportExponent-3) Z ∧
       (∀ j,F.SingleFiber j → ∀ a,F.twig j=.inl a→U j=Xo a)∧∀ j,¬ F.SingleFiber j → Blade (C.path.rep N p i) ((U j).home P.v) ((U j).oil P.v) (profile (C.path.rep N p i).activities ((U j).gas P.v)) 0 (4*(1/T j)):=by
    intro W Xo Z'; let S:= placeOn Xo (tabs F o' i); let A₀:= C.path
    have hf(a: I⊕Z): (S a).home=roots F o o' i a:=by
       cases a; exact (L _).hold.steers i (hk _) i.le_succ; rfl
    have hsx : pegs V I o i=tags Xo:= cover_homes L i.le_succ hk
    have hj : tags S=fun x=> roots F o o' i x.2 x.1:= funext fun x=> congr_fun (hf _) x.1
    choose c hY using fun a=> (L a).hold.routes i (hk a) i.lt_succ_self
    obtain ⟨T,hT,hU,hZ,hX⟩:= formation (D:=A.D N p i hn) F (tabs F o' i) H l χ χ' (hC ▸ h.owns) (A.admits hm.le hn) hA.wilson hn (A.stock hm hn.le) (A.arcPars hm.le) h.live (by linarith only) (fun j=>(L j).hold.marks i (hk _) i.le_succ) hY (L.rim ▸ G'.before) (hsx ▸ G'.after) (hj ▸ G'.allIn) (fun j=> hp (F.bunch (.inr j))) (fun j=> by change coverNumber _ ({tags S _, tags S j}:_) ≤ l; rw [hj]; dsimp only;  exact (congr_fun (G'.twig (F.bunch j.2)) j.1) ▸ G'.small j.2 j.1) G'.sizeP G'.sizes ht -- notation import ht/H
    refine ⟨T,fun j=> (hT j).trans ((hf _).trans (G'.twig j)), out_live _ (StepData.push_integrable (C.path.levels.transition_mass ..) _ h.live), hU,fun j hj a ht=> (hZ j hj).trans (by rw [ht]; rfl),hX⟩
end Lights
end YM.OPE.Allot
