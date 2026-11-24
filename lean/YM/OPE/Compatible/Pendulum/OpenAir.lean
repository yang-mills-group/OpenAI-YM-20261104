import YM.OPE.Compatible.Pendulum.Duplex
/-! Seats even on shifted partners. Care needed requiring only when accessible: apertures below k need *not* permit that shift. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Pixel
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave Relay Cells CutOrder
open scoped Topology BigOperators Classical
variable {X I : Type} [PartialOrder X][OrderBot X][Fintype X]
   {G:Gauge}{C:Family G}{p J k N b i:ℕ}{x:Site (C.side N p)}
lemma sign_width (b:Bool)(y z:Site (C.side N p)):width C N p (signBase C p N x y b) (signBase C p N x z b)=width C N p y z:=by
   unfold signBase width; split_ifs with h; rfl; simp [sub_eq_add_neg] -- want separation simp
-- compile Survey
variable {D:Origin X}{U:Finset X}{m j:X→ℕ} {l:ℕ→ℕ}{W:X→ Site (C.side N p)}
variable (S:Series U m)(L:Tactic C D U m j N p J b l W)(hv:m ⊥ ≤ k)(hn:k ≤ N)
    (h:∀ y:X,y∈allUp D U → width C N p (W y-x) 0≤ C.S.a J/4)
set_option quotPrecheck false
local notation "ρ"=> intoSky C p J
local notation "D!"=>fun y:X=>board C p J N x (W y)
local notation "A"=> Site (C.side J p) × Bool
include L hv hn h
lemma away_cloud (y z:X)(hy:y∈allUp D U)(hz:z∈allUp D U)(hk:k≤ i)(hi:i≤ N)(a b':Site (C.side J p))(f:Bool)(he:a≠b'): atLevel C i b ≤ separation (D! y i (a,f)) (D! z i (b',f)):=by
   have hJ:=L.live.trans hv; let w y:= signBase C p N x (W y) f
   have hz' i (hx:i∈allUp D U):width C N p (w i) 0≤ C.S.a J/4:=by unfold w signBase; split <;> first| exact L.seek i hx | exact h _ hx
   have hw:= spanCopies C p N J (w y) (w z) (hJ.trans hn) a b' he; have hu:= L.overflow i (hv.trans hk) hi; let t:= atLevel C i b
   have hp:= comp_width (V:=w y) (W:=w z) (hJ.trans hk) hi a b' (show (t+2:ℝ)*_ ≤ _ from by linarith only [hw,hz' y hy,hz' z hz,hu]); unfold width at hp; rw [mul_comm _ (C.S.a i)] at hp; exact_mod_cast le_of_mul_le_mul_left hp (C.S.a_pos _)
omit h hn in
lemma apart_cloud (y z:X)(hy:y∈allUp D U)(hz:z∈allUp D U)(hu:¬ y ≤ z)(hx:¬ z ≤ y)(hp:m (Arboreal.couple D y z)< i)(hk:k≤ i)(hi:i≤ N)(v:Site (C.side J p)×Bool): atLevel C i b ≤ separation (D! y i v) (D! z i v):=by
   have he:= L.split' y z hy hz hu hx i hp hi; let w y':=signBase C p N x (W y') v.2
   have hJ:J ≤ i:= L.live.trans (hv.trans hk); have hQ:width C N p (axis C p N J (w y) N v.1) (axis C p N J (w z) N v.1)=width C N p (W y) (W z):= (gap_width C p N J _ _ (hJ.trans hi) _).trans (sign_width ..)
   have hp:= comp_width hJ hi v.1 v.1 (he.trans hQ.symm.le); unfold width at hp; rw [mul_comm _ (C.S.a i)] at hp; exact_mod_cast le_of_mul_le_mul_left hp (C.S.a_pos _)
include S
omit h hn in
lemma ppCloud (y z:X)(hy:y∈U)(hz:z∈allUp D U)(hi:k ≤ m y)(hk:y≤ z)(hp:finishAt D m z=m y)(v:Site (C.side J p)×Bool): coverNumber (bins C (m y)).B ({D! y (m y) v,D! z (m y) v}:Support _)≤ 81*(l (m y)+1):=by
   let w y':= signBase C p N x (W y') v.2; let i:=m y; let a:=D! y N v; let b':=D! z N v
   have hy' : i≤ N:= (Series.high D S hy).trans L.when'.le; have hJ:J≤ i:= L.live.trans (hv.trans hi)
   have hh:= cellShift C p hy' a b'; rw [show (C.S.toDepth hy' p).parent a= D! y i v from congr_fun (parents_up C p N J (w y) hJ hy' le_rfl) v.1,show (C.S.toDepth hy' p).parent b'= D! z i v from congr_fun (parents_up C p N J (w z) hJ hy' le_rfl) v.1,(show width C N p a b'=width C N p (W y) (W z) from (gap_width C p N J (w y) (w z) (hJ.trans hy') _).trans (sign_width ..))] at hh
   let g:=separation (D! y i v) (D! z i v); let t:=bins C i
   refine Corona.linear_lane t.B_pos _ _ ?_
   have ht:C.S.a i*g ≤ C.S.a i*((l i:ℝ)*t.B):=by
      change width C i p (D! y i v) (D! z i v) ≤ _; rw [← mul_assoc]; have he:= L.coincide y z hy hz hk hp; change _ +_*C.S.a i ≤ C.S.a i*l i*t.B at he; linarith only [he,(abs_le.mp hh).1]
   exact_mod_cast le_of_mul_le_mul_left ht (C.S.a_pos _)
lemma breeze (hk: k≤ N)(w:Site (C.side k p))(ht:x=(C.S.toDepth hk p).embed w): Arcade C (clouds C p J) (intoSky C p J true) Prod.snd D U m j N p (listP C p J) (Mix.camp C p J) (fun i=>axis C p N J (W i)) b (fun i=>81*(l i+1)) (rootTilt C p J N x) (fun i=>board C p J N x (W i)) k:=by
   have he:= L.live.trans hv
   refine ⟨clocked D S W L,registerCloud ..,hn,tilt_moves C p J k N x he hn w ht,fun _ _ _=> rfl,fun _ _ _ _ _=>rfl,fun y i _ hi hw=>?_,fun y i _ hi hu v _=>?_,fun y i hy hi hu a b ht=> ?_,?_,fun x y _ =>apart_cloud L hv x y,ppCloud S L hv⟩
   · funext v; rw [ratio_same (C.S.toDepth (Nat.le_succ i) p) (C.path.levels.clock.op i p).ratio]; exact congr_fun (parents_up C p N J (signBase C p N x (W y) v.2) (he.trans hi) (Nat.le_succ i) hw) v.1
   · obtain ⟨T,hx⟩:= tilted C p i N x hi hn hu w ht; exact board_move C p J N i x (W y) (he.trans hi) hu _ hx v
   · rcases a,b with ⟨⟨a,s⟩,b',t⟩; obtain ⟨hp,hq⟩:= Prod.mk.inj ht; change s=t at hq; subst t
     by_contra hx; have hz:=away_cloud L hv hn h y y hy hy hi hu a b' s (fun h=>hx (h ▸ rfl)); dsimp only at hz; rw [hp,separation_self] at hz; have hψ:0< atLevel C i b:= Nat.mul_pos (by omega) (bins C i).B_pos; omega
   rintro x y i hx hy hk ht ⟨a,f⟩ ⟨v,e⟩ (he:f=e) hv'; subst f; exact away_cloud L hv hn h _ _ hx hy hk ht _ _ e (fun h=>hv' (h ▸ rfl))
end YM.OPE.Arboreal.Pixel
