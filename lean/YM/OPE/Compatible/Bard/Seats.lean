import YM.OPE.Compatible.Bard.Regalia
/-! Return shipment to main cut lane. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Arcade
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave Relay Cells
open scoped Topology BigOperators Classical
variable {X V I G' T W : Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X) {U F K:Finset X}{m j:X→ℕ}
    [Fintype V][DecidableEq V][Fintype T][DecidableEq T][Fintype G']
    {G:Gauge}{C:Family G}{p N b d k:ℕ}{l:ℕ→ℕ}{A:Allot C} {z e r:ℝ}
variable {P:Ensemble V}{P':Ensemble T}{E:Track C.path V p}{o:X→ Track C.path V p}
    {E':Track C.path T p}{o':X→Track C.path T p} {f:V ↪ T}{a:T→G'}
    {Q: Extra.Histories.Music (C.labels.level d) C.path N p}
variable (L:Arcade C P' f a D U m j N p P E o b l E' o' k)
    (S:Wave m U K (k+1))(S':Wave m K F k) (x:brim D F)(hP:x.val∈brim D K)(hX:x.val∈U)
set_option quotPrecheck false
local notation "I₀"=> (C.labels.level d).Index
local notation "P!"=> lantern C.path r d k
local notation "R"=> C.path.rep N p
include L hX S S' hP
variable {Y:Lights A P N p (inlet (W:=(C.labels.level d).Index) D F x.val m k) k b E (o∘ Wave.columns D (C.labels.level d).Index F x.val)}
variable {T₀:brim D F→Stem T G (C.S.side k p)} (v:T×(brim D F)→ Config G (C.S.side N p)→ℂ)
omit L hX S S' hP [PartialOrder X][OrderBot X][Fintype X] [Fintype V][DecidableEq V] in
private lemma align {a a':ℕ}(h:a=a')(o:Track C.path V p)(T:Line A P N p a k b E o) : ∃ T':Line A P N p a' k b E o,T'.X=T.X∧ T'.w=T.w:=by subst a';exact ⟨T,rfl,rfl⟩
omit [Fintype G'] S' in
lemma recession (hk:k≤ N) (h : Owned (curtain (brim D F) a) (C.path.rep N p k) (E' k) P' T₀ (update (fun i:brim D F=> Y.asks (.inl i)) x r) ((bins C k).supportExponent-3) (gust C.path N p N (birth (ManyCopies.Names T _) (C.path.rep N p N) v) k hk))
    (u:∀ i:ℕ, Coefficient (C.labels.level d) (C.S.side i p))(hs: Stamp (N:=N) P' (C.localSection d) (E' k) (u k) (T₀ x))
    (hL:Guided (C.localSection d) C.params C.path N p (C.ref d) k u A.D (lantern C.path r d k))
    (hU:Integrable (birth (ManyCopies.Names T _) (C.path.rep N p N) v) (prior G _)) (hr:0<r)
    (hy:(T₀ x).home = o' x.val k)
    (hc:∀ i,i≠x→ cropStem f (T₀ i)=Y.tips (.inl i))
    (hv:∀ x y,a (f x)=a (f y))
    (hz:j x.val ≤ k)(hh:C.ref d<j x.val)(hM:d ≤ b)(hG:G.Simple)(hA:C.Makes):
    let v':= v ∘ limb (brim D F) f
    Integrable (birth (ManyCopies.Names V _) (C.path.rep N p N) v') (prior G _)∧ ∃ T:Lights A P N p (fun i:brim D F=>finishAt D m i.val) k b E (fun i=>o i.val), LitUp T (CutOrder.full V _) (gust C.path N p N (birth (ManyCopies.Names V _) (C.path.rep N p N) v') k hk) ∧ T.bottom x=Run.Below C.path ((lantern C.path r d k (j x.val))/2) (j x.val) (finishAt D m x.val)∧ ∀ i:brim D F,i≠x → T.bottom i=Y.bottom (.inl i):=by
   intro g; let w:= update (fun i:brim D F=>Y.asks (.inl i)) x r; let z(i):=cropStem f (T₀ i); let x':brim D K:=⟨x.val,hP⟩; have hT := L.bed; have hb:m x.val=k+1:= S.taken D x' hX; let B:= finishAt D m; let i':= j x.val
   have he:E' k∘f=E k:= L.turns _ le_rfl hk
   have hV : o' x.val k∘f=o x.val k:= L.honors _ _ (mem_union_left _ hX) le_rfl hk
   have hₓ: m ⊥ ≤ B x.val:= lower_earliest D U m hT.plan _ (mem_union_left _ hX)
   have hc': B x.val ≤ i':= hT.epochs _ hX |>.1
   obtain ⟨T₂,hS,hσ,hF⟩:= Allot.keep_on (E:=E) A _ hA hG hL (show Stamp (N:=N) P _ (E k) (u k) _ from he ▸ Stamp_rotate_down L.fly hs)
      (show (z x).home= o x.val k from by change (T₀ x).home ∘ f=_;rw [hy,hV]) hr (hT.head.le.trans hₓ) hh hc' hz hM ⟨fun i hi hx=> (hT.inHost _ hX).mare i hi (hx.trans_le (k.le_succ.trans hb.ge))⟩ ⟨fun i hi hx=> hT.moves.mare i (hₓ.trans hi) (lt_of_lt_of_le (lt_of_lt_of_le hx hz) hk)⟩ (fun i hi hp=> hT.pare _ (mem_union_left _ hX) i hi (hp.trans_le (hz.trans ((k.le_succ.trans hb.ge).trans (if_pos hX|>.ge))))) (fun i hi hp=> hT.echo _ (mem_union_left _ hX) i (hc'.trans hi) (hp.trans ((k.le_succ.trans hb.ge).trans (if_pos hX|>.ge))))
   have hB(i:brim D F):∃ T':Line A P N p (B i.val) k b E (o i.val), T'.X k=z i∧ T'.w k ≤ w i∧ (i=x→ T'.w (B i.val)=Run.Below C.path (P! i'/2) i' (B x.val))∧(i≠x→ T'.w (B i.val)= Y.bottom (.inl i)):=by
       by_cases hi:i=x
       · subst i; exact ⟨T₂,hS,hσ.trans_le (le_trans (div_le_self hr.le one_le_two) ((show w x=r from update_self ..)|>.symm.le)),fun _=> hF,fun h=>False.elim (h rfl)⟩
       have he: inlet (W:=I₀) D F x.val m k (Sum.inl i)=B i.val:=by unfold inlet brimEnd; dsimp only [Sum.elim]; exact update_of_ne (Subtype.val_injective.ne hi) ..
       obtain ⟨x,hx,h₂⟩:= align he (o i.val) (Y (.inl i)); refine ⟨x,(congr_fun hx k).trans (hc i hi).symm,(congr_fun h₂ k).trans_le ?_,fun hh=>False.elim (hi hh),fun _=>?_⟩
       exact ((show w i=Y.asks (.inl i) from update_of_ne hi r (fun i : brim D F=>Y.asks (.inl i)))|>.ge)
       exact (congr_fun h₂ (B i.val)).trans (congr_arg (Y (.inl i)).w he.symm)
   choose X' hx hx' hZ' hG using hB
   have hh(p:(ManyCopies.Names V ↥(brim D F)).Mode) : (curtain ↥(brim D F) a).safe (imageM (limb (brim D F) f) p):=by
       rintro t ht v hv'; obtain ⟨⟨v',i⟩,_,rfl⟩:= mem_image.mp ht; obtain ⟨⟨z,v⟩,_,rfl⟩:=mem_image.mp hv'; exact hv _ _
   let X0:Lights A P N p (fun i:brim D F=> B i.val) k b E (fun i=>o i.val):=X'
   have hv:= wedged f L.fly h (χ':=CutOrder.full V _) (fun i _=>hh i)
   rw [narrower _ hU,station, he,← show X0.tips= fun i=>cropStem f (T₀ i) from funext hx] at hv
   have hY: Integrable (birth (ManyCopies.Names V _) (C.path.rep N p N) g) (prior G _):= (station (limb (brim D F) f) (C.path.rep N p N) v) ▸ (((Mirror.trim (limb (brim D F) f)).toContinuousLinearMap.restrictScalars ℝ).integrable_comp hU)
   exact ⟨hY,X0,⟨gust_live _ _ _ _ _ hY _,Owned.inhibit _ hv (fun i=>X0.asks_pos i) (fun i=>hx' i)⟩,hZ' _ rfl,hG⟩
end YM.OPE.Arboreal.Arcade
