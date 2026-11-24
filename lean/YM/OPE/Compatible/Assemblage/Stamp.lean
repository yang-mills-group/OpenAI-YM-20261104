import YM.OPE.Compatible.Assemblage.RoughLeg
/-!
# Stamped sources and arbitrary-offset ends of aligned intervals
-/
set_option autoImplicit false
set_option linter.unusedSectionVars true
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Stem
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {G : Gauge}{H:History G}{n m d N p k i:ℕ}{Z:Labels.Frame G d}{E₀:Hol G}{V :Type} [Fintype V][DecidableEq V]
variable (P:Ensemble V)(F:SectionData Z)
set_option quotPrecheck false
local notation "θ"=> H.rep N p i
-- scaling central report. `Radiated` relative to REF P.v orbit. For duplicated tilings each type and v can use this identity; require all copy data coil from x_v.
structure Stamp (E:V→Site (H.S.side i p))(Y:Coefficient Z (H.S.side i p)) (X:Stem V G (H.S.side i p)) : Prop where
    homes : Marked (H.rep N p i) E P X
    real' : X.oil P.v= radiant (alto H i d) (1,false) (X.home P.v) (Y.exponentialEntry 0 F (H.rep N p i))
    price : profile (H.rep N p i).activities (X.gas P.v)= sunny (H.rep N p i) Y.forced (1,false) (X.home P.v) (alto H i d)
lemma real_alto (m:Motion)(i:ℕ): scalar m (alto H i d)=alto H i d:=by unfold alto Motion.scalar; split <;> simp
namespace Stamp
variable {x:E4} {P} {E:V→Site (H.S.side i p)}{Y:Coefficient Z (H.S.side i p)}{g:Stem V G (H.S.side i p)}{t δ:ℝ} (h:Stamp (N:=N) P F E Y g)
include h
omit h in
lemma rays {V : Type} [Fintype V] [DecidableEq V] {P : Ensemble V} (F : SectionData Z)
    {E : V → Site (H.S.side i p)} {Y : Coefficient Z (H.S.side i p)} {g : Stem V G (H.S.side i p)}
    (h : Stamp (N:=N) P F E Y g) (j:V) : g.oil j = radiant (alto H i d) (P.move j) (g.home j) (Y.exponentialEntry 0 F θ)∧ profile (θ).activities (g.gas j)= sunny θ Y.forced (P.move j) (g.home j) (alto H i d):=by
   by_cases hp : j=P.v; · subst j; rw [P.spring]; exact ⟨h.real',h.price⟩
   have he:= h.homes.shine j hp; rw [he.1,he.2,h.real',h.price,h.homes.sym j hp]; unfold radiant sunny
   rw [scale_F,scale_K,flyF,flyK,real_alto]; exact ⟨rfl,rfl⟩
lemma equals_gauge (he:H.Selected)(hN:i≤N)(hδ:F.Sound E₀)(hg:Y.Format 0 E₀ (θ))(hy:Y.remBound 0 (θ) δ t)(j:V): g.sub θ j= radiant (alto H i d) (P.move j) (g.home j) (Y.density 0 F θ):=by
   obtain ⟨k,hK,hU,hV⟩:= sparkling H E₀ F Y (P.move j) (g.home j) (alto H i d) he 0 hN hδ hg hy; obtain ⟨hf,hk⟩:= h.rays F j; refine Eq.trans ?_ hV; change coin θ _ _ = _; rw [hf]; exact coin_port _ _ (h.homes.spends _) hU (hk.trans hK) (he.represents N p i hN|>.good.labels)
end Stamp
section
variable {X:Coefficient Z (H.S.side i p)} {E:V→Site (H.S.side i p)} {t δ:ℝ} (o:V→Site (H.S.side i p)) (he:H.Selected)(hN:i ≤ N)
include he hN
lemma realize (h:∀ j,j≠P.v→ o j=affine (P.move j).1 (E j) (o P.v))(hx:X.Format 0 E₀ (H.rep N p i))(hp:X.remBound 0 (H.rep N p i) δ t)(hf:F.Sound E₀):
    ∃ Y:Stem V G (H.S.side i p), Stamp (N:=N) P F E X Y∧ Y.home=o:=by
   obtain ⟨k,hK,hW,hU⟩:= sparkling H E₀ F X (1,false) (o P.v) (alto H i d) he 0 hN hf hx hp
   obtain ⟨Y,hY,hf,hk,hh⟩:= submit he hN (radiant (alto H i d) (1,false) (o P.v) (X.exponentialEntry 0 F (H.rep N p i))) hW o h; refine ⟨Y,⟨hY,hh.symm ▸ hf,?_⟩,hh⟩ -- radiance input specify
   rw [hh,hk]; exact hK.symm
end
section
variable {q r: ℝ}{w:ℕ→ℝ}{D: GaugeDoor (H.rep N p (i+1)) (H.rep N p i)}
variable (X: Coefficient Z (H.S.side i p)) (Y: Coefficient Z (H.S.side (i+1) p))
variable {g:Stem V G (H.S.side (i+1) p)}{g':Stem V G (H.S.side i p)}
    {E:V→Site (H.S.side (i+1) p)} {E':V→Site (H.S.side i p)}
local notation "B"=> H.rep N p (i+1)
variable (hH:H.Selected)(hi:i<N)(hF:F.Sound E₀)
   (hy: Y.Format 0 E₀ (H.rep N p (i+1))) (hy': Y.remBound 0 (H.rep N p (i+1)) (Real.sqrt (H.levels.clock.forcedAllowance (i+1))) r)(hx: X.Format 0 E₀ (H.rep N p i))(hx':X.remBound 0 (H.rep N p i) (Real.sqrt (H.levels.clock.forcedAllowance i)) q)
   (hD:SoundDoor (H.levels.clock.op i p) D)
   {Z':ℝ} -- remove
   {p':Set Wing}(hp:Tale p' 0 0 (((H.S.block i).val:ℂ)^d) (Y.exponentialEntry 0 F (H.rep N p (i+1))) (profile (H.rep N p (i+1)).activities Y.forced) (profile (H.rep N p i).activities X.forced) (Y.x 0) Z' q D)
-- independent from Fi/kappa_ for this proof
include hi hp hD hH
lemma stamped_hop (hs:p'.Finite)(p₀:Site (H.S.side i p)): let a := H.levels.clock.op i p; let s:= a.ratio.embed p₀
    let z:= alto H (i+1) d; let t:= alto H i d
    ∃ w:Set Wing,w.Finite∧ Tale w s p₀ 1 (radiant z (1,false) s (Y.exponentialEntry 0 F (H.rep N p (i+1)))) (sunny (H.rep N p (i+1)) Y.forced (1,false) s z) (sunny (H.rep N p i) X.forced (1,false) p₀ t) (z*(Y.x 0)) (‖z‖*Z') (‖t‖*q) D:=by
    intro A S z t; obtain ⟨Z⟩:= (hH.represents N p (i+1) hi).good.labels.moves 1 S
    have he:= (hp.gain hD (1,false) p₀ Z (show _ from rfl)).pitch z t (alto_at H i d)
    simp only [affine,Signed.act_zero,zero_add] at he; exact ⟨_,hs.image _,he⟩
include hF hy hy' hx hx'
-- witness Journey with priced Tales retained
lemma one_hop (h:Stamp (N:=N) P F E Y g)(h':Stamp (N:=N) P F E' X g')(hs:p'.Finite)(hL : (H.levels.clock.op i p).ratio.embed ∘ g'.home=g.home)(hd:X.density 0 F θ= blast H N p i d (Y.density 0 F (H.rep N p (i+1))))
    {t:ℝ}(hξ:t*‖alto H (i+1) d*(Y.x 0)‖≤1)(hb:2*t*(‖alto H (i+1) d‖*Z')≤1)(hw:t*(‖alto H i d‖*q)≤1): Journey D (H.levels.clock.op i p) P g g' t (alto H (i+1) d*(Y.x 0)):=by
    let a:=H.levels.clock.op i p; let z:= alto H (i+1) d; refine ⟨funext (fun i=>?_), fun j=>?_, ?_,hξ⟩
    · change a.ratio.parent _ = _; rw [← congr_fun hL i]; exact a.ratio.embed_parent _
    · rw [Stamp.equals_gauge F h hH hi hF hy hy' j,Stamp.equals_gauge F h' hH hi.le hF hx hx' j,← hL];
      exact starship H (P.move j) (g'.home j) (alto H i d) (Y.density 0 F (H.rep N p (i+1))) _ hd (play_integrable H N hH hi hy hy') _ (alto_at ..)
    obtain ⟨p₀,hP,hQ⟩:= stamped_hop F X Y hH hi hD hp hs (g'.home P.v); rw [h.real',h.price,h'.price, ← hL]; exact ⟨_,hP, ‖alto H (i+1) d‖*Z',_, hb,hw,hQ⟩
end
end YM.MergeProof.Ribbons.ManyCopies.Stem
