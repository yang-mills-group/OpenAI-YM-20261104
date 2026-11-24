import YM.OPE.Compatible.Bower.Bridge
/-!
# Full Guard geometry presweep and availability through folds. Doesn't assume simultaneous `axes` remain pairwise distinct at capture.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Arcade
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave
open scoped Topology BigOperators Classical
variable {X V I G' T : Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X) {U Q F K:Finset X}{v:X} {m j:X→ℕ}
    (W:Type)[Fintype V][DecidableEq V][Fintype I][DecidableEq I][Fintype W][DecidableEq W][Fintype T][DecidableEq T][Fintype G']
    {G:Gauge}{C:Family G}{p n N b d k g:ℕ}{l:ℕ→ℕ}{A:Allot C}
variable {P:Ensemble V}{P':Ensemble T}{E:Track C.path V p}{o:X→ Track C.path V p}
    {E':Track C.path T p}{o':X→Track C.path T p} {f:V ↪ T}{a:T→G'}
variable (h:Arcade C P' f a D U m j N p P E o b l E' o' k)
private lemma scarf {x y:X}(hp: Crown Q)(hx:x∈ allUp D Q)(h:¬ x ≤ y) : Arboreal.couple D x y∈ Q:=by
    have ht:= separate_left D h; rcases Finset.mem_union.mp hx with hh|hh; exact hp.roots ht.le hh; exact hp.roots (touch_par D ht) ((on_brim ..).mp hh|>.2.2)
include D W h
local notation "A!"=> places X+Fintype.card W
set_option quotPrecheck false
-- before n=s n≥ all. h needs ≥, invoke
omit [Fintype V][DecidableEq V][Fintype G'] in
lemma sturdy (hv:v∈U)(hk:whenHigh U m ≤ n)(ht:k≤ n) : Margins (shades' D U v a W) b (n+1) N (o' ∘ Wave.columns D W U v):=by
   let I:=brim D U; let J:= ↥(brim D U)⊕W; let F:= Wave.columns D W U v
   have hA(j:J): F j ∈allUp D U:= front' D W (mem_union_left _ hv) (Finset.Subset.refl _) j -- replace
   intro i hi hh x hx t hp w he hv'; rcases t,w with ⟨⟨t,b'⟩,w,l⟩; rcases hx with ⟨hz,hr,hp'⟩
   have hu:k ≤ i:=le_trans ht (show n ≤ i from le_of_lt hi) -- hi notation
   by_cases hQ:t=w; swap; · exact h.seats (F b') (F l) i (hA _) (hA _) hu hh.le t w (hz _ hp _ he) hQ
   subst w
   have he' : b'≠l:=fun H=>hv' (H ▸ rfl)
   have hx(v z:J) (hp:¬ F v ≤ F z)(hq:¬ F z ≤ F v): atLevel C i b ≤ separation (o' (F v) i t) (o' (F z) i t):=by
       have he:v∈ (univ: Finset J):= mem_univ _; exact h.interval _ _ i (hA _) (hA _) hp hq ((Series.high D h.bed.plan (scarf D h.bed.plan.base (hA v) hp)).trans hk|>.trans_lt hi) hu hh.le t -- diverge import atlas? derive
   have hs{k:brim D U}:¬ k.val ≤ v:=fun he=> ((on_brim ..).mp k.2).1 (h.bed.plan.base.roots he hv)
   cases b'
   next y=> cases l
            next z=>
               have he: y≠z:= fun h=> he' (h ▸ rfl); have hu':=Subtype.val_injective.ne he; exact hx (.inl y) (.inl z) (brim_apart D U h.bed.plan.base y.2 z.2 hu') (brim_apart D U h.bed.plan.base z.2 y.2 hu'.symm)
            next z=> exact hx (.inl y) (.inr z) (hs (k:=y)) (hp' t z y he hp)
   next y=> cases l
            next z=> exact hx (.inr y) (.inl z) (hp' t y z hp he) (hs (k:=z))
            next z=> exact False.elim (he' (congr_arg _ (hr t y z hp he)))
-- viability. allIn count. foci.
omit [Fintype V][DecidableEq V][DecidableEq T] in
lemma extendable (S:Wave m F K n)(he:F⊆U)(hv: v∈ allUp D U)(hn:n<N)(hk:k ≤ n)(ht: Fintype.card G'*(places X+Fintype.card W) ≤ A.r n)(hh:1 ≤ l n):
    Incoming A (riseUp W D S) (o'∘ columns D W F v) (o' ∘ columns D W K v) n (places X+Fintype.card W) (l n):=by
   let J:= riseUp W D S; let L':= columns D W F v; let P':= columns D W K v; let U':= roots J (o' ∘ L') (o'∘ P') n
   let g(i:(brim D F⊕W)⊕(starts D F K)):= i.elim L' (fun z=> P' (J.bunch (.inr z)))
   have hI i : g i∈allUp D U:=by
       cases i; next i=>exact front' D W hv he i
       next i=> exact front D W S hv he (J.bunch (.inr i))
   have hf(v'): U' v'=o' (g v') n:=by cases v'<;>rfl
   have hB(i:brim D K⊕ W) : g (J.twig i)= P' i:=by
       cases i
       next x=>
          by_cases he':x.val∈F
          · rw [take_new D S x he']; rfl
          obtain ⟨a,ha,hx⟩:=take_left D S x ((solos W ..).2 he'); rw [ha]; exact hx
       rfl
   have hu: Fintype.card ((brim D F⊕W)⊕(starts D F K))≤A!:=by rw [Fintype.card_sum,Fintype.card_sum,Fintype.card_coe,Fintype.card_coe]; exact le_trans (le_of_eq (by omega)) (Nat.add_le_add_right (places_dom (brim D F) (starts D F K)) _)
   have h_f(x:Site (C.path.S.side n p)):coverNumber (bins C n).B ({x,x}:Support _)≤ l n:=by
        have ht:= (bins C n).B_pos; simp only [Finset.insert_eq_of_mem (s:={x}) (mem_singleton_self _)]; exact (le_trans ((Corona.cover_mono (halo_subset 0 {x}) _).trans (show coverNumber (bins C n).B (Lattice.halo 0 {x}) ≤1 from by simpa using Lattice.Corona.tile x 0 (bins C n).B ht)) hh)
   refine ⟨fun i=>?_,begun D W h he hv (hk.trans n.le_succ) hn ht,begun D W h he hv hk hn.le ht,?_,fun j v' => ?_,hu,(places_pos X).trans_le (Nat.le_add_right ..)⟩
   · change U' _=(o' (P' i)) n; rw [hf,hB]
   · have hx': pegs T ((brim D F⊕W)⊕(starts D F K)) (o'∘ g) n=(fun i:T×_=> U' i.2 i.1):=funext fun i=> (congr_fun (hf i.2) i.1).symm
     exact hx' ▸ cover D h g hI hk hn.le ((by rw [Fintype.card_prod]; exact (Nat.mul_le_mul_left _ hu).trans ht))
   change coverNumber _ ({o' (P' (J.bunch j)) n v',U' j v'}:Support _)≤_
   cases j
   next x=>
       cases x
       next x=>
           show coverNumber _ ({o' ((topHat D S x).val) n v',o' x.val n v'}:Support _) ≤ _
           by_cases hv:(topHat D S x).val∈ F
           · have he':= S.taken D _ hv; have hf:= h.share _ _ (he hv) (brim_under D U F he x.2) (hk.trans he'.symm.le) (S.visits D x) ((S.children D x hv).trans he'.symm) v'; rw [he'] at hf; exact hf
           have hq': (topHat D S x).val = x.val:=by by_contra hx'; exact brim_apart D F S.before.base (S.sweep D (topHat D S x).2 hv) x.2 hx' (S.visits D x)
           rw [hq']; exact h_f _
       exact h_f _
   exact h_f _
end YM.OPE.Arboreal.Arcade
