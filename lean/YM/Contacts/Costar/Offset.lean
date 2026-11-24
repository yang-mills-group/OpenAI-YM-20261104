import YM.Contacts.Costar.Wide
import YM.MergeProof.West.News
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Costar
open Function Set Filter MeasureTheory Extraction Extraction.Spin Cells Lattice Wilson Word MergeProof.Ribbons Next.Phase
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}(C:Family G){b k t l N p m : ℕ}

lemma pays_side (h:k ≤ l)(he:l ≤ N) (n:ℕ) (hv:(n:ℝ)*C.S.a l < C.S.a k): n*span C.S he p < span C.S (h.trans he) p:= by
   apply (Nat.cast_lt (α:=ℝ)).1; apply lt_of_mul_lt_mul_left _ (C.S.a_pos N).le; rw [Nat.cast_mul,mul_left_comm]
   rwa [C.S.embeds_scale (C.S.toDepth (h.trans he) p),C.S.embeds_scale (C.S.toDepth he p)]

lemma location_zero : location C.S k N p 0=0:=by unfold location; split; simp_rw [map_zero, ← Ratio.root_embed,map_zero];rfl
private lemma zero_inside (hk:b ≤ N) (v:Cover) (u r:ℕ) (hv: ∀ i,(v i).natAbs ≤ u) (hx: 2*(u+r) < span C.S hk p):
    let T:= center C.S p hk 0
    (0:Site (C.side N p))∈ (T.newly (T.base+wrap (C.side N p) v)).margin 0 r:=by
   intro T; let U:= T.newly (T.base+wrap (C.side N p) v); let B:= T.side.val
   let t i:ℤ:= (↑(B/2):ℤ)-v i
   have hx: 2*(u+r)<B:=hx
   have he i: r ≤ t i ∧ t i + r < B:=by unfold t; have :=hv i; omega
   have hh i: (↑(U.coordinated 0 0 i):ℤ)=t i:= by
       have hs:= U.narrow; have ht:= he i; have hN:B< (C.side N p).val:=hs
       have hP : (t i).toNat < (C.side N p).val:=by omega
       have hy : ((t i).toNat:ℤ)=t i:=by omega
       have hE : (0:Site (C.side N p)) i-U.starts 0 i=((t i).toNat:Per (C.side N p)):=by
          rw [U.starts_zero]; change 0 - ( (0:Per (C.side N p))-((↑(B/2):Per _)) + (v i:Per (C.side N p)))=_
          conv_rhs => rw [← Int.cast_natCast,hy]
          dsimp only [t]; rw [Int.cast_sub, Int.cast_natCast]; abel
       change (↑((_-_ : Per _).val):ℤ)=_; rw [hE,ZMod.val_natCast_of_lt hP]; exact hy
   refine ⟨fun i=>?_,fun i=> ?_⟩
   · change U.coordinated 0 0 i<B; have hh:= hh i; have :=he i; omega
   change r ≤ U.coordinated 0 0 i ∧ U.coordinated 0 0 i+r+1≤B; have hh:= hh i; have := he i; omega

lemma allocates (hb:b ≤ k)(hl:k ≤ l)(ht:l ≤ t)(hx:t ≤ N)(y:Fin m→ Site (C.side N p))
    (hh: 8*C.S.a k < C.S.a b) (hs: (6*m:ℝ)*C.S.a t < C.S.a l):
    ∃ (o:Site (C.side N p)), let T:= (center C.S p (hb.trans ((hl.trans ht).trans hx)) 0).newly o; let L:= (center C.S p (ht.trans hx) 0).newly o;
       0∈T.margin 0 (3*span C.S ((hl.trans ht).trans hx) p) ∧ ∀ i, Next.Phase.Inside L (3*span C.S hx p) (y i):=by
   have hY : k ≤ N:=(hl.trans ht).trans hx; let M:= 3*span C.S hx p
   have hg:Fintype.card (Fin m)*(2*M) < span C.S (ht.trans hx) p:= by
       have ht : (6*m:ℕ)*span C.S hx p< _ := pays_side C ht hx (6*m) (by push_cast; exact hs)
       rw [Fintype.card_fin]; dsimp only [M]; convert ht using 1; ring
   let T:= center C.S p (hb.trans hY) 0; let L:= center C.S p (ht.trans hx) 0
   obtain ⟨w,hw,H⟩:= Next.Phase.shift_into L y T.base rfl M (Nat.mul_pos (by decide) (C.S.toDepth hx p).count.property) hg
   refine ⟨T.base+wrap _ w,?_ ,H⟩
   let B:= span C.S hY p
   have ht': 2*(B+3*B)<span C.S (hb.trans hY) p := by have hs:= pays_side (p:=p) C hb hY 8 (by norm_cast); unfold B; omega
   exact zero_inside C (hb.trans hY) w B (3*B) (fun i=> le_trans (hw i).le (Nat.le_of_dvd (C.S.toDepth hY p).count.property (Around.inherits (C:=C) hl (ht.trans hx)))) ht'
lemma at_centers (x:Cover)(hb:b≤k)(hl:k≤t)(ht:t ≤ N)(he: (7:ℝ)*C.S.a t< C.S.a k):
    let T:= center C.S p (hb.trans (hl.trans ht)) 0; let U:= (center C.S p (hl.trans ht) 0).newly T.base
    Next.Phase.Inside U (3*span C.S ht p) (location C.S k N p x):=by
   intro T U; let v:= location C.S k N p x
   let X:=span C.S ht p; let L:= span C.S (hl.trans ht) p; let G:= span C.S (hb.trans (hl.trans ht)) p
   obtain ⟨b',h⟩:= C.S.toDepth_odd (hl.trans ht) p; change L=2*b'+1 at h
   obtain ⟨k',h'⟩:= C.S.toDepth_odd hb p; have hg:G=L*(2*k'+1):= by rw [← h']; exact Work.B15.count_trans (C.S.toDepth (hl.trans ht) p) (C.S.toDepth hb p) _
   have hn:G/2= L*k'+b' := by
       have hs:G=2*(L*k'+b')+1:=by rw [hg,h];ring
       omega
   have ht' : 7*X<L:=pays_side C hl ht 7 (by norm_cast); have he i: U.hom (v i-T.base i)=(↑b':Per U.side):=by
       have hu: U.side.val=L:=rfl
       have hL: (↑L:Per U.side) = 0:=by rw [← hu]; exact ZMod.natCast_self _
       have hy i : v i= (L:Per (C.side N p))*(x i:Per (C.side N p)):=by
          dsimp only [v,location]; rw [dif_pos (hl.trans ht), Ratio.embed_wrap]; simp [wrap,L]
       rw [map_sub,hy i]; change _ - U.hom (0-(↑(G/2):Per _))= _
       rw [hn, map_mul, map_sub,map_natCast, map_zero, map_natCast, Nat.cast_add, Nat.cast_mul,hL]; ring
   rw [inside_stripe U (by rfl)]; intro i; have hy : (Next.Phase.stripe U v i).val=b':= by unfold Next.Phase.stripe; change (U.hom (v i-T.base i)).val=_;rw [he];exact ZMod.val_natCast_of_lt (show b'<L by omega)
   rw [hy]; change 3*X ≤ b' ∧ b'+3*X<L;omega
end YM.Contacts.Costar
