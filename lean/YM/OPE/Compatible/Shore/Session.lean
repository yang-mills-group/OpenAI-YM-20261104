import YM.OPE.Compatible.Shore.Tour
/-!
# Session: lift selected steps across both displaced tilings, with
common data. R lines carry (possibly long) entire budgets.
Movement in meet away from the root alignment need only last actual
steps, not the full resulting promises. Can specialize to many tilings.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot
open Function Filter Lattice RG Wilson MeasureTheory MergeProof
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem Lights
open scoped Topology Classical
-- cleanup
variable {V I J W : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
   [Fintype W][DecidableEq W]{G:Gauge}{C: Family G}{HH:RG.History G}{N p m n i b:ℕ}
variable {A:Allot C}{P:Ensemble V}(P': Ensemble W)(M:V ↪ W)
    {O:I→ Track C.path V p}{E:Track C.path V p} {k:I→ℕ}

structure Session (L:Lights A P N p k n b E O) (Y:Config G (C.side n p)→ Marker.Poly (Names W I))
    (X:I→ Stem W G (C.S.side n p))(χ:Guard (Names W I))(E':Track C.path W p)(O':I→ Track C.path W p) : Prop where
    live : Integrable Y (prior G _)
    seen : ∀ i,cropStem M (X i)= L.tips i
    stood i : (X i).home=O' i n
    ship : Owned χ (C.path.rep N p n) (E' n) P' X L.asks ((bins C n).supportExponent-3) Y
namespace Session
variable {P' M} {O':I→Track C.path W p}{E':Track C.path W p} {χ:Guard (Names W I)}
-- frame one step (outside movement, origins). first datum from Session.S

set_option quotPrecheck false
structure Coast (M:V ↪ W)(P:Ensemble V)(P': Ensemble W) (k j:ℕ) (E:Track HH V p)(E':Track HH W p)(o:I→Track HH V p) (o':I→ Track HH W p): Prop where
   emb : Screenlet P P' M
   ring : Migrating HH k p j E'
   slot n : k ≤ n → n ≤ j→ E' n ∘ M=E n
   live i n : k ≤ n→ n ≤ j→ o' i n ∘ M=o i n
   match' i n:k ≤ n → n ≤ j→ ∀ v,v≠P'.v→ o' i n v=affine (P'.move v).1 (E' n v) (o' i n P'.v)
   back i n : k ≤ n→ n < j→ (HH.levels.clock.op n p).ratio.parent ∘ o' i (n+1)=o' i n
omit [Fintype V][Fintype W][Fintype I][DecidableEq V][DecidableEq I][DecidableEq W] in
lemma Coast.sub {M:V ↪ W}{U:Ensemble V}{y z:ℕ} {o:I→Track HH V p}{o' E' E}
   (p' : Coast M U P' y z E E' o o')(hp:y ≤ i)(he:m ≤ z): Coast M U P' i m E E' o o':=
   ⟨p'.emb,⟨fun _ hy hz=> p'.ring.mare _ (hp.trans hy) (hz.trans_le he)⟩,
   fun n hk hi=>p'.slot n (hp.trans hk) (hi.trans he),fun i n hk hi=>p'.live i n (hp.trans hk) (hi.trans he),fun i n hk hi=>p'.match' i n (hp.trans hk) (hi.trans he),fun i n hk hi=>p'.back i n (hp.trans hk) (hi.trans_le he)⟩
section

variable {L:Lights A P N p k N b E O}
set_option maxHeartbeats 150000 in
lemma begin_p (H:C.Makes)(C': Coast M P P' N N E E' O O') (χ:Guard (Names W I)) (f:W×I→ Config G (C.side N p)→ℂ)(hf:∀ i, Budges P C.path N p (far C.path.levels N) (L.asks i) (E N) (L.tips i) (fun a=>f (M a,i)))
    (h:∀ a, Continuous (f a)) (he:∀ i v,v≠P'.v→f (v,i)=stepUp (P'.move v) (E' N v) (f (P'.v,i))) (hX:Occupancy (pegs W I O' N) (A.r N)):
    ∃ X,Session P' M L (birth (Names W I) (C.path.rep N p N) f) X χ E' O':=by
   have hp (i:I): (L.tips i).home=O' i N∘M:= (L.steered i).trans (C'.live i N le_rfl le_rfl).symm
   have hv: E' N ∘M= E N:= C'.slot _ le_rfl le_rfl
   choose X hK hx hg using fun i=> discovered M C'.emb (O' i N) H.wilson le_rfl (hp i) (C'.match' i N le_rfl le_rfl) ((hv).symm ▸ (hf i).mark)
   let g(i:I)(j:W):= f (j,i); have hu(i:I): Budges P' C.path N p (far C.path.levels N) (L.asks i) (E' N) (X i) (g i):=by
       refine Budges.covers M C'.emb H.wilson (hg i) ?_ (fun v=>he i v); rw [hK,hv]; exact hf i
   have hY: Integrable (birth (Names W I) (C.path.rep N p N) f) (prior G _):= (hatCont C N p _ h (show Continuous (C.path.rep N p N).eval by rw [(H.wilson.starts ..).2]; exact bare_cont _) (Names W I)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
   have hT:pegs W I O' N=tags X:=funext fun i=> (congr_fun (hx i.2) i.1).symm
   have hI:= flushed (X:=X) hu H.wilson A.buy.system.costs.night (hT ▸ hX); refine ⟨X,hY,hK,hx,?_⟩; have hb: (fun t:W×I=>g t.2 t.1)=f:=funext fun i=>by cases i; rfl
   rw [hb] at hI; exact { issues := ⟨_,hY,fun _ _ _=>rfl,hI⟩ }
end
section
variable {L:Lights A P N p k (n+1) b E O}{X:I→ Stem W G (C.S.side (n+1) p)} {Y:Config G (C.side (n+1) p)→Marker.Poly (Names W I)}
   (H:C.Makes)(S:Session P' M L Y X χ E' O') (C': Coast M P P' n (n+1) E E' O O')(he:∀ i,k i≤ n)
set_option quotPrecheck false
local notation "U" => L.lowers he n.le_succ
local notation "R"=> C.path.rep N p
local notation "Z"=> C.path.levels.clock.op n p
include H S C' he
lemma along (hn:n < N):∃ X':I→ Stem W G (C.S.side n p),
    (∀ i,cropStem M (X' i)= (U).tips i)∧(∀ i,(X' i).home=O' i n)∧ (∀ i, Marked (R n) (E' n) P' (X' i))∧
      ∃ c:I→ℂ,∀ i,Journey (A.D N p n hn) Z P' (X i) (X' i) (L.asks i) (c i):=by
    have hp i:= (C'.live i n le_rfl n.le_succ).symm; have hv:= (C'.slot n le_rfl n.le_succ).symm
    choose X' hX hx hT using fun i=> discovered M C'.emb (O' i n) H.wilson hn.le (((U).steered i).trans (hp i)) (C'.match' i n le_rfl n.le_succ) (hv ▸ (L i).hold.marks n (he i) n.le_succ)
    choose c hc using fun i=> (L i).hold.routes n (he i) n.lt_succ_self
    refine ⟨_,hX,hx,hT,c,fun i=>?_⟩
    refine Journey.extended M C'.emb H.wilson hn ((C'.ring.mare n le_rfl n.lt_succ_self).symm ▸ S.ship.known χ i) (hT i) ?_ (S.ship.pay_part H.wilson hn (P'.v,i)) ?_
    · rw [S.stood,hx]; exact C'.back i n le_rfl n.lt_succ_self
    rw [S.seen,hX]; exact hc i
lemma drift (hp:C.ref 0 ≤ n)(hn:n<N)
    (ht:Margins χ b n (n+1) O') (hA: Occluded A n (n+1) O') (hχ:χ.Chordal P'.v P'.perms) : ∃ X', Session P' M (L.lowers he n.le_succ)
      ((Z).push (R (n+1)).beta Y) X' χ E' O' :=by
    let Γ:= C.path; have he':= A.admits (p:=p) hp hn; let v:= renal C.path.levels n; obtain ⟨X',hX,hP,hY,c,hc⟩:= S.along H C' he hn
    have hv: pegs W I O' (n+1)= tags X:= funext fun i=> (congr_fun (S.stood i.2) i.1).symm; have hx: pegs W I O' n= tags X':=funext fun i=> (congr_fun (hP i.2) i.1).symm
    have hh:= ht n le_rfl n.lt_succ_self; rw [hx] at hh
    let v:= renal C.path.levels n
    refine ⟨_,StepData.push_integrable (C.path.levels.transition_mass ..) _ S.live,hX,hP, refill P' χ ((C'.ring.mare n le_rfl n.lt_succ_self).symm ▸ S.ship) S.live H.wilson hn he' (by linarith only) hY hc (hv ▸ (hA n le_rfl n.lt_succ_self).1) (hx ▸ (hA n le_rfl n.lt_succ_self).2) hχ (U|>.asks_pos) (Guard.lanes χ hh (fun j=> mul_pos he'.staff.hats.1 (L.asks_pos j.2)) (fun j=> (U).asks_pos j.2) (fun j=>?_ ) (C.path.levels.budget n).B_pos)⟩
    exact gap_hi C _ _ ((L j.2).guard' n (he _) n.lt_succ_self) (L.asks_pos _)
end
end Session
end YM.OPE.Allot
