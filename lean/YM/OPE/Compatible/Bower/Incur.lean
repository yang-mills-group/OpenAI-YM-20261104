import YM.OPE.Compatible.Bower.Toll
/-!
# Apply the temporary route and read out at k with prefix still shared
Outputs prices just on requested peers, carry counter axis receipts.
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
    {G:Gauge}{C:Family G}{p N b d k:ℕ}{l:ℕ→ℕ}{A:Allot C}
variable {P:Ensemble V}{P':Ensemble T}{E:Track C.path V p}{o:X→ Track C.path V p}
    {E':Track C.path T p}{o':X→Track C.path T p} {f:V ↪ T}{a:T→G'}
variable (h:Arcade C P' f a D U m j N p P E o b l E' o' k)
    (S:Wave m U K (k+1))(S':Wave m K F k) (x:brim D K)(hx: x.val∈U) (hX:x.val∈ brim D F)
set_option quotPrecheck false
local notation "r"=>fun (F:Finset X)=> o∘columns D W F x.val
local notation "r'"=>fun (F:Finset X)=> o'∘columns D W F x.val
local notation "χ"=>fun F=>shades' D F x.val a W
local notation "kX"=> fun F=>brimEnd D W F (finishAt D m) k
local notation "iX"=>fun F=>inlet (W:=W) D F x.val m k
local notation "n"=>k+1 -- times
local notation "sX"=> update (brimEnd D W K (finishAt D m) k) (Sum.inl x) (k+1)
local notation "jX"=> update (brimEnd D W K j k) (Sum.inl x) (k+1)
local notation "v'"=>(⟨x.val,hX⟩:brim D F)
local notation "N'"=> C.ref d
local notation "H"=>places X+Fintype.card W
local notation "δ"=>fun a':ℝ=>C.S.a (k+1)^d*(β C (k+1)*(4*(1/a')))
def spurs {W:Type}[Fintype W][DecidableEq W] {D':Type} [CommMonoid D'] (y: T×(brim D F⊕ W)→ D') (S:Wave m F K k)(x:T×(brim D K⊕W)):= ∏ j∈(raised W D S).contents x.2,y (x.1,j)
def feedS (S:Wave m F K k)(y:brim D F→ℝ) (Y:ℕ)(e:ℝ)(x:brim D K):= event_fee Y e * ∏ i∈ (elements D S).contents x,y i
lemma batch_card (W:Type)[Fintype W] (F K:Finset X): Fintype.card ((brim D F ⊕ W) ⊕ starts D F K) ≤ places X + Fintype.card W:=by rw [Fintype.card_sum,Fintype.card_sum,Fintype.card_coe,Fintype.card_coe]; have h:= places_dom (brim D F) (starts D F K); omega
lemma feed_pos {Y:brim D F→ℝ} (S:Wave m F K k) (x:brim D K)(b:ℕ){e:ℝ}(he:0<e)(hy:∀ a,0<Y a):0 < feedS D S Y b e x:=mul_pos (pow_pos he _) (prod_pos fun _ _=>hy _)
-- final gate after charges from temp
variable {e Y:ℝ}
include h S S' hx hX
lemma roll_bill (hA:C.Makes)(hG:G.Simple)(hn:k+1 ≤ N)(hp:C.ref 0 < k)(hd: 1 ≤ l k)(hc: Fintype.card G'*H ≤ A.r k)
    (he:0 < e)(hu:e ≤ valve C H b (l k) k)
    (hh:∀ i:brim D F, i.val∈K→ e ≤ Run.Below C.path (sash C k/2) (j i.val) (finishAt D m i.val))
    (Q:Lights A P N p (inlet (W:=W) D K x.val m k) (k+1) b E (r K)) (f₀:T×(brim D K ⊕ W)→ Config G (C.side N p)→ℂ)
    (hΓ : Integrable (birth (ManyCopies.Names T _) (C.path.rep N p N) f₀) (prior G _)) {X₀}
    (hZ: Session P' f Q (gust C.path N p N (birth (ManyCopies.Names T _) (C.path.rep N p N) f₀) (k+1) hn) X₀ (shades' D K x.val a W) E' (r' K)):
    let f₁:=spurs D f₀ S'
    Integrable (birth (ManyCopies.Names T _) (C.path.rep N p N) f₁) (prior G _) ∧
    ∃ T':Lights A P N p (inlet (W:=W) D F x.val m k) k b E (r F), ∃ X', Session P' f T' (gust C.path N p N (birth (ManyCopies.Names T _) (C.path.rep N p N) f₁) k (show k≤ N from lt_of_lt_of_le k.lt_succ_self hn|>.le)) X' (shades' D F x.val a W) E' (r' F) ∧
       (∀ i:brim D F, i.val ≠ x.val → feedS D S' (fun i=> Q.bottom (Sum.inl i)) H e i ≤ T'.bottom (Sum.inl i)) ∧
       e*Q.bottom (Sum.inl x) ≤ T'.asks (Sum.inl v') ∧ T'.tips (Sum.inl v')=(Q (Sum.inl x)).X k ∧ (∀ i:W, e*Q.bottom (.inr i) ≤ T'.asks (Sum.inr i) ∧ T'.tips (Sum.inr i)=(Q (Sum.inr i)).X k):=by
   intro y; obtain ⟨hj,Z,w,hG,h'⟩:= rolled D h S S' x hx hX hA hG hn hp hd hc hΓ hZ; let V':=riseUp W D S'; let u':=elements D S'; have hy: y=(fun i z=> ∏ j∈ (raised W D S').contents i.2, f₀ (i.1,j) z):=funext fun i=>funext fun U=> prod_apply ..; have hW := held D (W:=W) h S S' x hx hX hn
   rw [hy]; have hr(i:brim D F)(hi:i.val≠ x.val): iX F (Sum.inl i)=finishAt D m i.val:= by dsimp only; unfold inlet brimEnd; dsimp only [Sum.elim]; apply update_of_ne hi k (finishAt D m)
   let v:= v'
   have h : (riseUp W D S').SingleFiber (.inl v):=(solos W ..).mpr ((on_brim ..).mp x.2|>.1)
   have hv': V'.twig (.inl v)= .inl (.inl x):=by obtain ⟨i,hx,ht⟩:=take_left D S' _ h; exact (Subtype.ext ht:i=x) ▸ hx
   have hI: iX F (Sum.inl v)=k:=by change update (finishAt D m) x.val k v.val=_; unfold v; exact update_self x.val k (finishAt D m)
   have ht1 : Z.bottom (Sum.inl v)= Z.asks (Sum.inl v):=congr_arg (Z (Sum.inl v)).w hI
   refine ⟨hj,_,_,hG,fun i hi=>?_,?_,congr_fun ((h'.inherited (.inl v) h (.inl x) hv').1) _,fun i=> ?_⟩ -- dummy
   · refine return_ticket D S' h' hW (batch_card D W K F) ((places_pos X).trans_le (Nat.le_add_right ..)) hp.le i he hu fun he=>?_
     change e ≤ Run.Below C.path (sash C k / 2) (j i.val) (iX F (.inl i)); rw [hr _ hi]; exact hh i he
   · rw [← ht1, Lights.bill_solo Q h' h hv' (he:=hI.trans (show k= iX K (.inl x) from (by change k=update (finishAt D m) x.val k x.val; exact Eq.symm (update_self x.val k (finishAt D m)))))] -- orientation
     exact mul_le_mul_of_nonneg_right hu (Q.bottom_pos _|>.le)
   exact ⟨check_counter D S' h' i rfl hu, congr_fun ((h'.inherited (.inr i) (pilots D S' _) _ (take_right D S' i)).1) _⟩
end YM.OPE.Arboreal.Arcade
