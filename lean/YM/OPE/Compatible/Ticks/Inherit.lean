import YM.OPE.Compatible.Ticks.Line
/-! First hop of long lane. Raw group (no subtraction), so continue
at weight ZERO. Also survives with high Q available to project at root.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot
open Function Filter Lattice RG MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat Mallow Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open scoped Topology Classical
variable {G:Gauge} {C:Family G}(A:Allot C) {V:Type} [Fintype V][DecidableEq V] (P:Ensemble V)
variable {N p d j k m:ℕ}{b w:ℝ}{E o:Track C.path V p}
-- arbitrary simple group, transposes
variable {X:Stem V G (C.S.side (m+1) p)}
lemma convert_path (hm:C.ref d ≤ m)(he:m<N)(h: C.Makes)(hv:0 ≤ b)(hw:0<w)(hb:4*w*b≤1)(ht:w*(β C (m+1)*b) ≤ 1)
    (hh: Marked (C.path.rep N p (m+1)) ((C.path.levels.clock.op m p).ratio.embed ∘ E m) P X)
    (hp: MergeProof.Float.Blade (C.path.rep N p (m+1)) (X.home P.v) (X.oil P.v) (profile (C.path.rep N p (m+1)).activities (X.gas P.v)) 0 b)
    (hq: (C.path.levels.clock.op m p).ratio.embed ∘ o m=X.home) : let c:= C.S.a (m+1)^d*(β C (m+1)*b)
                                                                  ∃ y: Coefficient (C.labels.level d) (C.side m p),(C.labels.level d).coeffSize y.x ≤ c∧ y.Format 0 C.params (C.path.rep N p m)∧ y.remBound 0 (C.path.rep N p m) (Real.sqrt ((C.path).levels.clock.forcedAllowance m)) c∧ ∃ X': Stem V G (C.S.side m p), X'.home=o m∧ Stamp (N:=N) P (C.localSection d) (E m) y X'∧ Journey (A.D N p m he) (C.path.levels.clock.op m p) P X X' w 0:=by
   intro c
   have hA:= A.redraw hm he (p:=p)
   have hZ:= A.buy.literal; obtain ⟨T,K,S,rfl⟩:=hZ.uses
   let C := Family.mk T (Next.Foundations.hol G) (Labels.frames G) (Next.Foundations.localSection G) K S
   have hz:1 ≤ β C (m+1):=(β_one ..).le
   obtain ⟨x,y,h',hb'⟩:= A.buy.system.costs.night.days N p m he; exact edition_leg h.wilson he hA h'.propagate hh hp hq hv hz hw (le_trans (le_of_eq (b:=4*w*b) (by ring)) hb) ht
-- attach aligned continuous sequence zero weight
open Extra.Histories MergeProof.Float
lemma received (hm:C.ref 0 ≤ m)(he:m<N)(hg:G.Simple)(h: C.Makes)(hv:0 < b)(hw:0<w)(hb:4*w*b≤1)(ht:w*(β C (m+1)*b)≤1)
    (hq:w*(24*(1+(C.path.levels.params m).columns)*(β C (m+1)*b)) ≤ fly C.path.levels 0 m)
    (hK:C.ref 0 ≤ k)(hk:k ≤ m)
    (hh:Marked (C.path.rep N p (m+1)) (E (m+1)) P X)(hp:Blade (C.path.rep N p (m+1)) (X.home P.v) (X.oil P.v) (profile (C.path.rep N p (m+1)).activities (X.gas P.v)) 0 b)
    (hO:o (m+1)=X.home) (hx:Migrating C.path k p (m+1) E)(hp':Migrating C.path k p (m+1) o)(hy:∀ i:ℕ,k ≤ i→ i ≤ m → ∀ j:V, j ≠ P.v → o i j= affine (P.move j).1 (E i j) (o i P.v)):
    ∃ R:Travel C.path V p, Run P A.D N p k (m+1) E o R (fun _=>w)∧R (m+1)=X ∧
      ∀ i:ℕ, C.ref 0 < i → k ≤ i→ i ≤ m → ∃ c:ℂ,w*‖c‖ ≤ 1 ∧ Blade (C.path.rep N p i) ((R i).home P.v) ((R i).oil P.v) (profile (C.path.rep N p i).activities ((R i).gas P.v)) c (1/w):=by
   have H:=h.wilson; have hv' : 0<β C (m+1)*b:=mul_pos (β_pos ..) hv
   obtain ⟨y,hY,hU,hV,X0,hY',h',hx'⟩:= convert_path A P hm he h hv.le hw hb ht ((hx.mare m hk m.lt_succ_self).symm ▸ hh) hp ((hp'.mare m hk m.lt_succ_self).trans hO)
   rw [pow_zero,one_mul] at hY hV
   let S:= A.buy.system; obtain ⟨M,hI,hS,hC,hH⟩ := (A.buy.system.costs.aim 0 N p (hm.trans he.le)).lyrics
   let Q:=2*(β C (m+1)*b); have hq' : 0<Q:=by unfold Q; positivity
   let r:=4*(1+(C.path.levels.params m).columns)*Q
   obtain ⟨Y,hY⟩:= fortuned S h M hS hC y (E:=r) hm he.le hU hV hq' (le_trans (add_le_add_left hY (β C (m+1)*b)) (le_of_eq (by unfold Q; ring))) (le_refl _)
   have hz:= leading_whole hY hS hV S hw (fun i hi hI=> by refine le_trans (le_trans ?_ hq) (fly_le hg 0 i m hI); exact le_of_eq (by unfold r Q; ring))
   have hs(i:ℕ)(he:i<N):= S.costs.night.days N p i he
   have hsX (i:ℕ)(hi:i<N):SoundDoor (C.path.levels.clock.op i p) (A.D N p i hi):= by obtain ⟨x,y,h',ht⟩:= hs i hi; exact h'.propagate
   obtain ⟨Z,hZ,h_X,hZ'⟩:= prints P (C.localSection 0) hz H (h.sections _) (fun i _=>hsX i) hK hk X0 (starting_whole hY hS hU hV h') hY' ⟨fun i hi hM=>hp'.mare i hi (lt_of_lt_of_le hM m.le_succ)⟩ hy
   let Q:=Function.update Z (m+1) X; have HH: Q (m+1)=X:=Function.update_self ..; have heq(i:ℕ)(hi:i ≤ m) : Q i= Z i:= Function.update_of_ne (Nat.lt_succ_of_le hi).ne ..
   refine ⟨Q,(hZ.shift (fun i hi hq=>⟨(heq i hq).symm,rfl,rfl⟩)).together (Run.mk (Nat.le_succ _) he (fun i _ _=>hw) ?_ ?_ ?_), HH, fun i hi hR hi' =>?_⟩
   · intro i hi hi'; rcases eq_or_ne i (m+1) with rfl|hN; exact HH.symm ▸ hh
     have ht:i ≤ m:=Nat.le_of_lt_succ (lt_of_le_of_ne hi' hN); exact heq i ht ▸ hZ.marks i (hk.trans hi) ht
   · intro i hi hi'; rcases eq_or_ne i (m+1) with rfl|hN; rw [HH,hO]
     have ht:i ≤ m:=Nat.le_of_lt_succ (lt_of_le_of_ne hi' hN); rw [heq _ ht, hZ.steers _ (hk.trans hi) ht]
   · intro i hi hq; obtain rfl:i=m:=by omega
     rw [HH,heq _ le_rfl,h_X]; exact ⟨0,hx'⟩
   cases i with
   | zero=>omega
   | succ i=>
      have ha:i<N:=by omega
      obtain ⟨x,y,t,ht⟩:= hs i ha; rw [heq _ hi']; exact ⟨_,hz.spice _ hi.le hi',root_cut P (C.localSection 0) hz H (fun i _=>hsX i) (by omega) hi' t.tunes _ (hZ' (i+1) hR hi')⟩
end YM.OPE.Allot
