import YM.OPE.Compatible.Portage.Ordering
/-!
# Exact chart in arbitrary mesh orientations and eventually volume

Realize a grid at given points at their specified lattices, every p large enough and N (after it) large enough. On lattice keep separation torus-compatible. Does not choose heights/s in actual limit functional.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Pixel
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float Next.Rank Station Next.Rank.Spindle
open Push Marker Local Extra.Histories Extra.Trajectories MeasureTheory Extra.Multi Finset Cells Ribbon
open scoped Topology Classical
variable {X:Type}[PartialOrder X][OrderBot X][Fintype X]
    (D:Origin X) {Q:Finset X} {G:Gauge}{C:Family G}{m k:X→ℕ}{N p J b W:ℕ} {l:ℕ→ℕ}(S: Series Q m)
open YM.OPE.Allot Series
variable (x:X→E4)
-- x is positioned on k x. final clock internal min to allow j cap.
-- top lift uses common W. cap at least max k, can exceed. only includes allUp, rest coordinates dummy
lemma same_place {a b:Site (C.side N p)}(h:C.S.place a=C.S.place b): a=b:=by
   have he : ∀ i,((lift a i:ℤ):ℝ)=(lift b i:ℤ):=by
      intro i; apply mul_left_cancel₀ (C.S.a_pos N).ne'; exact congr_fun (congr_arg WithLp.ofLp h) i
   have hf:lift a=lift b:= funext fun i=> by exact_mod_cast he i
   rw [← wrap_lift a, ← wrap_lift b, hf]
structure Positioned (C:Family G)(D:Origin X)(Q:Finset X)(m k:X→ℕ)(b J W:ℕ)(l:ℕ→ℕ)(x:X→ Cover) : Prop where
   wisp : C.ref 0 < m ⊥
   live : J ≤ m ⊥
   ap x : x∈ allUp D Q → finishAt D m x ≤ k x
   roofed x : x∈allUp D Q→k x ≤ W
   enabled y : y∈allUp D Q→∃ z:Cover,C.S.gridPoint W (x y)= C.S.gridPoint (k y) z
   belly : x ⊥=0
   fit y : y∈allUp D Q→ 8*‖C.S.gridPoint W (x y)‖ ≤ C.S.a J
   shells : ∀ i:ℕ,m ⊥ ≤ i→ (atLevel C i b +2 :ℝ)* C.S.a i ≤ C.S.a J/2
   apart u v : u∈allUp D Q → v∈allUp D Q → ¬ u ≤ v → ¬ v ≤ u→∀ i,m (couple D u v)< i → (atLevel C i b+2:ℝ)*C.S.a i * 2 ≤ ‖C.S.gridPoint W (x u)-C.S.gridPoint W (x v)‖
   cluster a v : a∈Q→ v∈allUp D Q→ a ≤ v→finishAt D m v=m a → ‖C.S.gridPoint W (x a)-C.S.gridPoint W (x v)‖ +2*C.S.a (m a)≤ C.S.a (m a)*l (m a) * (bins C (m a)).B
set_option quotPrecheck false
include D S
variable {y:X→ Cover} (h:Positioned C D Q m k b J W l y)
include h
lemma eventual_positioned : ∀ᶠ p:ℕ in atTop,∀ᶠ N:ℕ in atTop,
    let z i:= Cells.location C.S W N p (y i)
    let j i:=min (k i) (m i)
    Tactic C D Q m j N p J b l z∧ (∀ i∈allUp D Q, k i ≤ N)∧ (∀ i∈allUp D Q,∃ s:k i≤ N,∃ w:Site (C.side (k i) p), z i= (C.S.toDepth s p).embed w) ∧ z ⊥=0 ∧ ∀ i∈allUp D Q,C.S.place (z i)=C.S.gridPoint W (y i):=by
   choose! a ha using fun x hx=> h.enabled x hx
   filter_upwards [(Eventually.of_forall (fun _:ℕ=> trivial)), (eventually_all.mpr fun x:X => faraway C (k x) (a x)),(eventually_all.mpr fun x:X =>faraway C W (y x)),(eventually_all.mpr fun x:X =>width_yoke W (y x) 0 (C:=C)),(eventually_all.mpr fun x:X =>eventually_all.mpr (fun v:X =>width_yoke W (y x) (y v) (C:=C)))] with p _ hz ht hh hw
   filter_upwards [eventually_gt_atTop W, eventually_gt_atTop (whenHigh Q m)] with N hW hQ
   intro z j; let R:= C.S.toDepth hW.le p; have he(i):z i=R.embed (wrap (C.side W p) (y i)):= dif_pos hW.le
   have hs(i):C.S.place (z i)=C.S.gridPoint W (y i):= (congr_arg C.S.place (he i)).trans ((C.S.embeds_place ..).trans (ht i))
   have h0 : z ⊥=0:= by rw [he,h.belly,map_zero]; exact R.root.map_zero
   have hv x (hx:x∈allUp D Q): z x=(C.S.toDepth ((h.roofed x hx).trans hW.le) p).embed (wrap (C.side (k x) p) (a x)):= same_place ((hs x).trans ((ha x hx).trans ((hz x).symm.trans (C.S.embeds_place ..).symm)))
   refine ⟨⟨h.wisp,hQ,h.live,fun i hi=> ⟨le_min (h.ap i (mem_union_left _ hi)) (S.timing _ _ (par_le ..) hi),min_le_right ..⟩,fun i hi hx=> ?_, fun x hx=>?_,fun i hi _=> h.shells _ hi,fun x u hh heU Hx Hy i hv hi=> ?_,fun x u hx hy hep hzp=>?_⟩,
      fun i hi=> (h.roofed _ hi).trans hW.le,fun i hi=> ⟨_,_,hv _ hi⟩,h0,fun i _=>hs i⟩
   · rcases lt_or_ge (k i) (m i) with ht|ht
     · rw [show j i=k i from min_eq_left ht.le]; exact ⟨_,_,hv _ (mem_union_left _ hi)⟩
     exact False.elim (hx.ne (min_eq_right ht))
   · rw [he,← show R.embed 0=0 from R.root.map_zero,embed_width]; have hH:=hh x; rw [grid_zero] at hH; have he :width C W p (wrap (C.side W p) (y x)) 0 ≤ ‖C.S.gridPoint W (y x)‖:= by simpa using hH.1
     linarith only [norm_nonneg (C.S.gridPoint W (y x)),h.fit x hx,C.S.a_pos J,he]
   · rw [he, he, embed_width]; have hQ:=h.apart x u hh heU Hx Hy i hv; have hv:=(hw x u).2; linarith only [hQ,hv]
   · rw [he,he,embed_width]; have hd:=(hw x u).1; have ht:=h.cluster x u hx hy hep hzp; linarith only [hd,ht]
end YM.OPE.Arboreal.Pixel
