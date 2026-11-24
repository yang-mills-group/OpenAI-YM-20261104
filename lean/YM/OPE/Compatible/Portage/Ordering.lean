import YM.OPE.Compatible.Portage.Lifts
/-!
# Calibrated torus life given pattern emanating from the common block origin

Does not compare arbitrary distant points by using wrong relative-cell representatives.
Period clearance needed only at N, with physical lower-cost separations at clocks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Pixel
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float Next.Rank Station Next.Rank.Spindle
open Push Marker Local Extra.Histories Extra.Trajectories MeasureTheory Extra.Multi Finset Cells Ribbon
open scoped Topology Classical
variable {X:Type}[PartialOrder X][OrderBot X][Fintype X]
    (D:Origin X) {Q:Finset X} {G:Gauge}{C:Family G}{m j:X→ℕ}{N p J b:ℕ} {l:ℕ→ℕ}
open YM.OPE.Allot Series
variable (S: Series Q m)
-- enabled copy set (hcap CHT). Same grades startup. width of pegs from tap merged.
structure Tactic (C:Family G)(D:Origin X)(Q:Finset X)(m j:X→ℕ)(N p J b:ℕ)(l:ℕ→ℕ)(o:X→ Site (C.side N p)) : Prop where
   tip : C.ref 0 < m ⊥
   when' : whenHigh Q m < N
   live : J ≤ m ⊥
   tier x : x∈Q→ finishAt D m x ≤ j x ∧ j x ≤ m x
   invest x : x∈ Q → j x < m x→ ∃ h:j x≤N, ∃ y, o x= (C.S.toDepth h p).embed y
   seek x : x∈allUp D Q→ width C N p (o x) 0≤ C.S.a J/4
   overflow : ∀ i:ℕ,m ⊥ ≤ i → i≤N → (atLevel C i b + 2 :ℝ)* C.S.a i ≤ C.S.a J /2
   split' x y : x∈allUp D Q → y∈allUp D Q→ ¬ x ≤ y→ ¬ y ≤ x→∀ i, m (couple D x y)< i → i≤ N→ (atLevel C i b +2:ℝ)* C.S.a i≤ width C N p (o x) (o y)
   coincide x y : x∈Q→ y∈allUp D Q→ x ≤ y → finishAt D m y=m x → width C N p (o x) (o y)+2*C.S.a (m x) ≤ C.S.a (m x)*(l (m x))* (bins C (m x)).B
-- halo upper for project = linear l, multiply 81
lemma comp_width {V W:Site (C.side N p)}(hi:J ≤ b)(hb:b ≤ N)(x y:Site (C.side J p)) {l:ℝ} (ht: (l+2)*C.S.a b≤ width C N p (axis C p N J V N x) (axis C p N J W N y)) : l*C.S.a b ≤ width C b p (axis C p N J V b x) (axis C p N J W b y) :=by
   let T:= axis C p N J V; let U:= axis C p N J W
   have h : width C N p (T N x) (U N y)-width C b p (T b x) (U b y) ≤ 2*C.S.a b:=(abs_le.mp (show |width C N p (T N x) (U N y)-width C b p (T b x) (U b y)| ≤ 2*C.S.a b from by
       rw [← show (C.S.toDepth hb p).parent (T N x)= T b x from congr_fun (parents_up C p N J V hi hb le_rfl) x,← show (C.S.toDepth hb p).parent (U N y)= U b y from congr_fun (parents_up C p N J W hi hb le_rfl) y]; exact cellShift ..)).2
   change _ ≤ width C N p (T N x) (U N y) at ht; change _≤ width C b p (T b x) (U b y); linarith only [ht,h]
include D S
lemma clocked (o:X → Site (C.side N p))(h:Tactic C D Q m j N p J b l o) :
    CutOrder C (CutOrder.listP C p J) D Q m j N p (Mix.camp C p J) (fun x=>axis C p N J (o x)) b (fun i=>81*(l i+1)):=by
   let P:=CutOrder.listP C p J; let T (x:X):= axis C p N J (o x); let r:= m ⊥; have hk(x)(he:x∈allUp D Q): r ≤ finishAt D m x:=lower_earliest D Q m S x he
   have hi:r≤ N:= (high D S S.base.base).trans h.when'.le
   have hp(x:X) : roof Q m N x ≤ N:=by
      unfold roof; split
      next he=>exact (high D S he).trans h.when'.le
      next=>exact le_rfl
   have hK {i:ℕ}(a a': Site (C.side J p))(x y)(he:a≠a')(hv:x∈allUp D Q)(hv':y∈allUp D Q)(hI:r ≤ i)(ht:i≤ N): atLevel C i b ≤ separation (T x i a) (T y i a'):=by
      have hh := spanCopies C p N J (o x) (o y) (h.live.trans hi) a a' he; have hW := h.seek x hv; have hV:= h.seek y hv'; have hz:= h.overflow i hI ht
      let t:= atLevel C i b
      have hQ := comp_width (V:=o x) (W:=o y) (h.live.trans hI) ht a a' (show (t+2:ℝ)*_ ≤ _ from by linarith only [hh,hW,hV,hz]); change (t:ℝ)* _ ≤ width C i p (T x i a) (T y i a') at hQ; unfold width at hQ; rw [mul_comm _ (C.S.a i)] at hQ; exact_mod_cast (le_of_mul_le_mul_left hQ (C.S.a_pos _))
   refine ⟨S,h.tip,h.when',h.tier, uphill C J _ p N h.live, fun x he i hi hi'=>?_,fun x he i hi hw v _=>bit C J N p i (o x) (h.live.trans ((hk _ he).trans hi)) v true,fun x he=>?_,fun x hv i hy hz=>?_,fun x hv i hk hv' a a' he=> hK a a' x x he hv hv ((lower_earliest D Q m S _ hv).trans hk.le) (hv'.trans (hp _)),fun x y ha hb hx hy i hq tx ty hx' hy' a v => ?_,fun x y hx hy he ht v=>?_,fun x v _=>?_,fun x he=> by exact Nat.succ_le_of_lt (by positivity)⟩
   · rw [ratio_same (C.S.toDepth (Nat.le_succ i) p) (C.path.levels.clock.op i p).ratio]; exact parents_up C p N J (o x) (h.live.trans ((hk _ he).trans hi)) _ (show i+1≤N from hi'.trans_le (hp _))
   · rcases (h.tier x he).2.lt_or_eq with hh|hh
     · obtain ⟨hi,y,ht⟩:= h.invest x he hh; rw [ht]; exact ⟨fun i hi' hj=> (reel C p N J (h.live.trans ((hk _ (mem_union_left _ he)).trans (h.tier x he).1)) hi _).mare i hi' (hj.trans_le (high D S he|>.trans h.when'.le))⟩
     exact ⟨fun i hi h=>False.elim (by omega)⟩
   · intro a a' he; by_contra h'; have h:=hK a a' x x h' hv hv ((hk _ hv).trans hy) (hz.trans (hp _)); change T x i a=T x i a' at he; rw [he,separation_self] at h; have ht:0< atLevel C i b:= Nat.mul_pos (by omega) (bins C i).B_pos; omega
   · by_cases he:a=v; swap
     · exact hK a v x y he ha hb ((hk _ ha).trans tx) (hx'.trans (hp _))
     subst a; let t:= atLevel C i b
     have ht:(t:ℝ)* C.S.a i ≤ width C i p (T x i v) (T y i v):=comp_width (h.live.trans ((hk _ hb).trans ty)) (hx'.trans (hp _)) v v (le_trans (h.split' x y ha hb hx hy i hq (hx'.trans (hp _))) (gap_width C p N J (o x) (o y) (h.live.trans hi) _|>.symm.le))
     unfold width at ht; rw [mul_comm _ (C.S.a i)] at ht; exact_mod_cast le_of_mul_le_mul_left ht (C.S.a_pos _)
   · let i:=m x; have hi : i ≤ N:= (high D S hx).trans h.when'.le
     have hv':J ≤ i:= h.live.trans (S.timing _ _ bot_le hx); let a:=T x N v; let b':=T y N v; have ha:= cellShift C p hi a b'
     rw [show (C.S.toDepth hi p).parent a=T x i v from congr_fun (parents_up C p N J (o x) hv' hi le_rfl) v,show (C.S.toDepth hi p).parent b'=T y i v from congr_fun (parents_up C p N J (o y) hv' hi le_rfl) v] at ha
     let s:= separation (T x i v) (T y i v); let A:=bins C i; refine Corona.linear_lane A.B_pos _ _ ?_
     have hh:=h.coincide x y hx hy he ht; change _+_ ≤ C.S.a i*l i*A.B at hh; have hz:width C N p a b'=width C N p (o x) (o y):=gap_width C p N J (o x) (o y) (hv'.trans hi) _
     have hψ: C.S.a i*s ≤ C.S.a i*((l i:ℝ)*A.B):=by
        change width C i p (T x i v) (T y i v) ≤_; rw [← mul_assoc]; linarith only [hh,hz,(abs_le.mp ha).1]
     exact_mod_cast le_of_mul_le_mul_left hψ (C.S.a_pos _)
   let t:= (bins C (m x)).B; let w:=axis C p N J (o x) (m x) v
   exact le_trans ((Corona.cover_mono (halo_subset 0 {w}) _).trans (show coverNumber t (Lattice.halo 0 {w}) ≤1 from by simpa using Lattice.Corona.tile w 0 t (bins C _).B_pos)) (Nat.succ_le_of_lt (by positivity))
end YM.OPE.Arboreal.Pixel
