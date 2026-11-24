import YM.OPE.Compatible.Bower.Incur
/-!
# Bill & give to relay. Through the conversion selected independently
of any particular counter. `z` used to commission ≤ issued. thus can be fixed before cutoffs.
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
variable {X V I G' T W : Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X) {U F K:Finset X}{m j:X→ℕ}
    [Fintype V][DecidableEq V][Fintype W][DecidableEq W][Fintype T][DecidableEq T][Fintype G']
    {G:Gauge}{C:Family G}{p N b d k:ℕ}{l:ℕ→ℕ}{A:Allot C} {z e:ℝ}
variable {P:Ensemble V}{P':Ensemble T}{E:Track C.path V p}{o:X→ Track C.path V p}
    {E':Track C.path T p}{o':X→Track C.path T p} {f:V ↪ T}{a:T→G'}
variable (h:Arcade C P' f a D U m j N p P E o b l E' o' k)
    (S:Wave m U K (k+1))(x:brim D K)(hx: x.val∈U)
set_option quotPrecheck false
local notation "w"=>k+1
local notation "r"=>fun (F:Finset X)=> o∘columns D W F x.val
local notation "r'"=>fun (F:Finset X)=> o'∘columns D W F x.val
local notation "kX"=> fun F=>brimEnd D W F (finishAt D m) k
local notation "sX"=> update (brimEnd D W K (finishAt D m) k) (Sum.inl x) (k+1)
local notation "iX"=> inlet (W:=W) D K x.val m k
local notation "jX"=> update (brimEnd D W K j k) (Sum.inl x) (k+1)
local notation "H"=>places X+Fintype.card W
local notation "R"=> C.path.rep N p
local notation "δ"=>C.S.a (k+1)^d*(β C (k+1)*(4*(1/z)))
local notation "J"=> ↥(brim D K)⊕W
include S h hx
set_option maxHeartbeats 200000 in
lemma ship {L:Lights A P N p (brimEnd D W U (finishAt D m) k) N b E (o∘columns D W U x.val)}
    {F': T×(brim D U⊕ W)→ Config G (C.side N p)→ℂ} {X₀}
    (hs: Session P' f L (birth (ManyCopies.Names T _) (C.path.rep N p N) F') X₀ (shades' D U x.val a W) E' (o'∘ columns D W U x.val))
    (hA:C.Makes)(hG:G.Simple)(hn:k+1<N)(hk:C.ref d≤ k) (hp:C.ref 0 < k)(hd:1≤ l (k+1))(ht:∀ i,k ≤ i→ Fintype.card G'*H ≤ A.r i)(hy:j x.val ≤ k)(hm:m ⊥ ≤ k) (he:0 < e)(hu:e ≤ valve C H b (l (k+1)) (k+1))(he':e≤ sash C (k+1)/2)(hh:∀ i:brim D K,i≠x→ i.val∈U→ e ≤ Run.Below C.path (sash C (k+1)/2) (j i.val) (finishAt D m i.val)) (hz:0 < z)(hθ:z≤ feedS D S (fun i=>L.bottom (.inl i)) H e x):
    let y':=spurs D F' S
    Integrable (birth (ManyCopies.Names T _) (C.path.rep N p N) y') (prior G _) ∧ ∃ y:Coefficient (C.labels.level d) (C.side k p), y.Format 0 C.params (R k) ∧ (C.labels.level d).coeffSize y.x≤δ ∧ y.remBound 0 (R k) (kappa C.path k) δ ∧
    ∃ T':Lights A P N p (inlet (W:=W) D K x.val m k) (k+1) b E (r K), ∃ X', Session P' f T' (gust C.path N p N (birth (ManyCopies.Names T _) (C.path.rep N p N) y') (k+1) hn.le) X' (shades' D K x.val a W) E' (r' K) ∧
       (∀ i:brim D K, i≠x → feedS D S (fun i=> L.bottom (.inl i)) H e i ≤ T'.bottom (Sum.inl i)) ∧
       T'.bottom (.inl x)=badge_fee C z k ∧ Stamp (N:=N) P (C.localSection d) (E k) y ((T' (Sum.inl x)).X k)∧ ∀ i:W, e*L.bottom (.inr i) ≤ T'.bottom (.inr i)∧ (T' (Sum.inr i)).X=(L (Sum.inr i)).X:=by
    intro V₀; obtain ⟨hh',U',X',hT',f₀,hW⟩:= depart D h S x hx F' hn k.le_succ (hp.trans_le k.le_succ) hd ht hA hG hs
    let M:= L.lowers f₀ hn; have hf:= xMain D (W:=W) h S x hx k.le_succ hn; let i0:J:= .inl x
    have hx(i)(he:i≠i0): iX i=sX i:=by rw [inlet_port D K x,update_of_ne he,update_of_ne he]
    -- avoid shadow
    have hI:sX i0=k+1:=by unfold i0; rw [update_self] -- `i0`
    have hJ:jX i0=k+1:=by unfold i0; rw [update_self]
    have hb(i:brim D K) : feedS D S (fun i=> L.bottom (.inl i)) H e i ≤ U'.bottom (.inl i):=by
       refine return_ticket D S hW hf (batch_card D W U K) ((places_pos X).trans_le (Nat.le_add_right ..)) (hp.trans_le k.le_succ|>.le) i he hu fun he0=> ?_
       by_cases he : i=x; · subst i; rw [hI,hJ,Run.below_main]; exact he'
       rw [update_of_ne (Sum.inl_injective.ne he),update_of_ne (Sum.inl_injective.ne he)]; exact hh i he he0
    have hx' : x.val ∈ U:=by assumption
    have hBL:= hW.blades (.inl x) ((solos ..).not.mpr (not_not_intro hx'))
    have hv: Migrating C.path k p (k+1) (o x.val):=⟨fun i hi hj=> h.bed.inHost x.val hx'|>.mare _ (hy.trans hi) (hj.trans_le (S.taken D x hx'|>.symm.le))⟩
    have hQ:iX i0=k:=by unfold inlet brimEnd; change update (finishAt D m) x.val k x.val=k; rw [update_self]
    have hY: z ≤ U'.asks (.inl x):=le_trans hθ ((hb x).trans_eq (congr_arg (U' (.inl x)).w hI))
    obtain ⟨p,hP,hF,hV,T',hT,hp,hZ,hR⟩:= warmup hA i0 hT' hQ hx hk ((show k< N from k.lt_succ_self.trans hn)) ⟨fun i hi hj=> h.bed.moves.mare _ (hm.trans hi) (hj.trans hn)⟩ hv hBL hz hY
    have heq: V₀=(fun i U'=>∏ j∈(raised W D S).contents i.2, F' (i.1,j) U'):=funext fun i=>funext fun U'=>prod_apply ..
    rw [heq]; refine ⟨hh',p,hP,hF,hV,T',_,hT,fun i hi=>?_,hp,hZ,fun j=>?_⟩
    · have he : Sum.inl i≠ i0:= Sum.inl_injective.ne hi; exact (hb i).trans_eq (by unfold bottom; rw [(hR _ he).1,hx (.inl i) he])
    let j':J:= .inr j; have hj : j' ≠ i0:= by intro h; contradiction
    have hk': sX j'=k:=update_of_ne hj ..; have hπ:= hR j' hj; have hv': e*L.bottom (.inr j) ≤ U'.bottom j':= check_counter D S hW j hk' hu
    refine ⟨hv'.trans_eq ?_, hπ.2.trans ((hW.inherited j' (pilots D S j) _ (Wave.take_right D S _)).1)⟩
    unfold bottom; rw [hπ.1]; exact congr_arg _ hk'
end YM.OPE.Arboreal.Arcade
