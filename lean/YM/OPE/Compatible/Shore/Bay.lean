import YM.OPE.Compatible.Shore.Session
/-!
# Session persists at first erosions, and even through folds. Carries
actual continuation receipts for R copies unaffected by this step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot.Session
open Function Filter Lattice RG Wilson MeasureTheory MergeProof
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem Lights
open scoped Topology Classical
variable {V I J W W': Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
   [Fintype W][DecidableEq W]{G:Gauge}{C: Family G}{N p m n i b:ℕ}
variable {A:Allot C}{P:Ensemble V}{P': Ensemble W}{M:V ↪ W}
    {O:I→ Track C.path V p}{E:Track C.path V p} {k:I→ℕ}
    {O':I→Track C.path W p}{E':Track C.path W p}{χ:Guard (Names W I)}
section
set_option quotPrecheck false
variable {L:Lights A P N p k n b E O}
   {X:I→Stem W G (C.side n p)}{Y:Config G (C.side n p) → Marker.Poly (Names W I)}
lemma cruise (h:Session P' M L Y X χ E' O') (H:C.Makes)(hn:n ≤ N) (hk:m ≤ n)
    (he:∀ i,k i ≤ m)(h₀:C.ref 0 ≤ m)(C': Coast M P P' m n E E' O O') (ht:Margins χ b m n O') (hA:Occluded A m n O') (hχ:χ.Chordal P'.v P'.perms) :∃ X', Session P' M (L.lowers he hk)
       (gust C.path N p n Y m hk) X' χ E' O':=by
    suffices H:∀ (u:ℕ)(hp:u≤n)(hz:m ≤ u),∃ X',Session P' M (L.lowers (fun i=>(he i).trans hz) hp) (gust C.path N p n Y u hp) X' χ E' O' by
        exact H m hk le_rfl
    intro u hu; induction hu using Nat.decreasingInduction with
    | self=>
       intro hp; rw [gust_base]; exact ⟨X,h.live,h.seen,h.stood,h.ship⟩
    | of_succ i hi ih=>
       intro hm; obtain ⟨Z,hZ⟩:= ih (hm.trans i.le_succ); obtain ⟨Y,hY⟩:= hZ.drift H (C'.sub hm hi) (fun x=>(he x).trans hm) (h₀.trans hm) (hi.trans_le hn) (fun j hu hx=>ht j (hm.trans hu) (hx.trans_le hi)) (fun j hu hx=>hA j (hm.trans hu) (hx.trans_le hi)) hχ; rw [gust_step _ _ _ _ _ hi]; exact ⟨Y,hY⟩ -- hY defeq cut
end
section
variable [Fintype J][DecidableEq J][Fintype W'][DecidableEq W']
set_option quotPrecheck false
variable {L:Lights A P N p k (n+1) b E O} {X:I→Stem W G (C.S.side (n+1) p)} {Y:Config G (C.S.side (n+1) p)→Marker.Poly (Names W I)}
    {C₀:J→Track C.path V p}{C₁:J→Track C.path W p}{χ':Guard (Names W J)}{k' j:J→ℕ}{F:Fibers (I⊕W') J}{H l:ℕ}
lemma dock (S:Session P' M L Y X χ E' O')(hG:G.Simple)(hC:C.Makes)(hn:n < N) (hv:C.ref 0<n)
    (C': Coast M P P' n (n+1) E E' O O') (D': Coast M P P' n n E E' C₀ C₁)
    (hR:Bind C P E F O C₀ n k k' j)(hV:Incoming A F O' C₁ n H l) (ht:∀ a,χ'.safe a→χ.safe (assembly F a)) : ∃ S', ∃ X':J→ Stem W G (C.S.side n p), Session P' M S' (reunion F ∘ (C.path.levels.clock.op n p).push (C.path.rep N p (n+1)).beta Y) X' χ' E' C₁ ∧ Issues L l H F (S':Lights A P N p k' n b E C₀) j:=by
   obtain ⟨U,hU,hP,hh,c,hX⟩:= along hC S C' hR.fell hn
   let Γ:= C.path.rep N p; let e:= C.path.levels.clock.op n p; let P'':= reunion F∘ e.push ((Γ (n+1)).beta) Y
   let Xo:= placeOn U (tabs F C₁ n)
   have hf(a: I⊕W'): (Xo a).home=roots F O' C₁ n a:=by cases a; exact hP _; rfl
   have hq:pegs W I O' (n+1)= tags X:= funext fun i=> (congr_fun (S.stood i.2) i.1).symm; have hx: pegs W I O' n= tags U:= funext fun i=> (congr_fun (hP i.2) i.1).symm
   have hj : tags Xo=fun x=> roots F O' C₁ n x.2 x.1:= funext fun x=> congr_fun (hf _) x.1
   obtain ⟨a',ha,hM,hl,hw⟩:= formation F (tabs F C₁ n) H l χ χ' ((C'.ring.mare n le_rfl n.lt_succ_self).symm ▸ S.ship) (A.admits hv.le hn) hC.wilson hn (A.stock hv hn.le) (A.arcPars hv.le) S.live (by linarith only) hh hX (hq ▸ hV.before) (hx ▸ hV.after) (hj ▸ hV.allIn) (fun j=> D'.match' (F.bunch (.inr j)) n le_rfl le_rfl) (fun j=> by change coverNumber _ ({tags Xo _,tags Xo j}:_)≤ l; rw [hj]; dsimp only; exact (congr_fun (hV.twig (F.bunch j.2)) j.1) ▸ hV.small j.2 j.1) hV.sizeP hV.sizes ht
   let Y' i:= cropStem M (a' i); have hs(i:J): (a' i).home=C₁ i n := (ha i).trans ((hf _).trans (hV.twig i))
   obtain ⟨S',hK,hs',hZ⟩:= commission L hR Y' hG hC hn.le hV.sizeP hv (fun i=> (congr_arg (fun f:W→_=>f ∘ M) (hs i)).trans (D'.live i n le_rfl le_rfl)) (fun i=> (D'.slot _ le_rfl le_rfl) ▸ Marked.high M (hM.known χ' i) C'.emb) (fun i he o ht=> by unfold Y'; rw [hl i he,ht]; exact hU o) (fun i he=>by specialize hw i he; rw [← C'.emb.start] at hw; exact hw)
   refine ⟨S',a',⟨out_live _ (StepData.push_integrable (C.path.levels.transition_mass ..) _ S.live),fun i=>(hK i).symm,hs,hM.inhibit χ' (S'.asks_pos) hs'⟩,hZ⟩
end
end YM.OPE.Allot.Session
