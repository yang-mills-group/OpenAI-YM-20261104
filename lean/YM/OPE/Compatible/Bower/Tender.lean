import YM.OPE.Compatible.Bower.Docket
/-! One inter-Wave ticket. Closed at k on original assembly. -/
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
    (S:Wave m U K (k+1))(S': Wave m K F k)(x:brim D K)(hx: x.val∈U)(hX:x.val∈ brim D F)
set_option quotPrecheck false
-- pruned peers
local notation "H"=> places X+Fintype.card W
local notation "R"=> C.path.rep N p
local notation "δ"=>C.S.a (k+1)^d*(β C (k+1)*(4*(1/z)))
local notation "v'"=>(⟨x.val,hX⟩:brim D F)
structure Taxes (C:Family G)(D:Origin X)(U:Finset X)(m j:X→ℕ)(l:ℕ→ℕ)(k H' b:ℕ)(e:ℝ) : Prop where
   start : 0< e
   sail : 1≤ l k∧ 1≤ l (k+1)
   spot : e ≤ sash C (k+1)/2
   interest i : k≤ i→ i≤ k+1→ e≤ valve C H' b (l i) i
   duty i : i∈U→ e ≤ Run.Below C.path (sash C (m i) /2) (j i) (finishAt D m i)
include h hx S S' hX
set_option maxHeartbeats 200000 in
lemma scene {L:Lights A P N p (brimEnd D W U (finishAt D m) k) N b E (o∘columns D W U x.val)}
    {F': T×(brim D U⊕ W)→ Config G (C.side N p)→ℂ} {X₀}
    (hs: Session P' f L (birth (ManyCopies.Names T _) (C.path.rep N p N) F') X₀ (shades' D U x.val a W) E' (o'∘ columns D W U x.val))
    (hA:C.Makes)(hG:G.Simple)(hn:k+1<N)(hk:C.ref d≤ k) (hp:C.ref 0 < k)(ht:∀ i,k ≤ i→ Fintype.card G'*H ≤ A.r i)(hy:j x.val ≤ k)(hm:m ⊥ ≤ k)
    {p': brim D U → ℝ} (ha:∀ a,0 < p' a)(hL:∀ y,p' y ≤ L.bottom (.inl y))
    (hC: Taxes C D U m j l k H b e)(hz:0 < z)(hθ:z≤ feedS D S p' H e x):
    let Y:=spurs D (spurs D F' S) S'
    Integrable (birth (ManyCopies.Names T _) (C.path.rep N p N) Y) (prior G _) ∧ ∃ y:Coefficient (C.labels.level d) (C.side k p), y.Format 0 C.params (R k) ∧ (C.labels.level d).coeffSize y.x≤δ ∧ y.remBound 0 (R k) (kappa C.path k) δ ∧
    ∃ T':Lights A P N p (inlet (W:=W) D F x.val m k) k b E (o∘ columns D W F x.val), ∃ X', Session P' f T' (gust C.path N p N (birth (ManyCopies.Names T _) (C.path.rep N p N) Y) k (le_trans k.le_succ hn.le)) X' (shades' D F x.val a W) E' (o'∘columns D W F x.val) ∧
       (∀ i:brim D F, i.val ≠ x.val → feedS D S' (feedS D S p' H e) H e i ≤ T'.bottom (Sum.inl i)) ∧
       e*badge_fee C z k≤ T'.asks (Sum.inl v') ∧ Stamp (N:=N) P (C.localSection d) (E k) y (T'.tips (.inl v'))∧ (∀ i:W, e^2*L.bottom (.inr i) ≤ T'.asks (Sum.inr i) ∧ T'.tips (Sum.inr i)=(L (Sum.inr i)).X k):=by
   intro u; let Y:=spurs D F' S
   have hm' i: feedS D S p' H e i ≤ feedS D S (fun i'=>L.bottom (.inl i')) H e i:= mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun j _=>(ha j).le) (fun j _=>hL j)) (pow_nonneg hC.start.le _)
   have hh:∀ i:brim D K,i≠x→ i.val∈U→ e ≤ Run.Below C.path (sash C (k+1)/2) (j i.val) (finishAt D m i.val):=by
      intro i hi hx; have hp:= hC.duty i.val hx; rw [S.taken D i hx] at hp; exact hp
   obtain ⟨hI,y,hP,hE,hR,S₂,Z,hU,hΓ,hK,hZ,hp'⟩:= ship D h S x hx hs hA hG hn hk hp hC.sail.2 ht hy hm hC.start (hC.interest _ k.le_succ le_rfl) hC.spot hh hz (hθ.trans (hm' x))
   obtain ⟨hY,T₀,Z',hq,he,hQ,ha',hΨ⟩:= roll_bill D h S S' x hx hX hA hG hn.le hp hC.sail.1 (ht _ le_rfl) hC.start (hC.interest _ le_rfl k.le_succ) (fun i ht=> (S'.taken D i ht) ▸ hC.duty i.val (S.next ht)) S₂ Y hI hU
   refine ⟨hY,y,hP,hE,hR,T₀,Z',hq,fun i he' => ?_,hK ▸ hQ,ha'.symm ▸ hZ,fun i=>?_⟩
   · apply le_trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hC.start.le (H+1))) (he i he'); apply Finset.prod_le_prod; exact fun _ _=> (feed_pos D S _ _ hC.start ha).le; intro j hj; refine le_trans (hm' _) (hΓ _ ?_); intro hx; subst j; exact he' (congr_arg Subtype.val ((Fibers.focuses ..).mp hj|>.symm.trans ((topper D S' x v').2 le_rfl))) -- infer typo
   refine ⟨le_trans (le_of_eq (b:=e*(e*L.bottom (.inr i))) (by ring)) ((mul_le_mul_of_nonneg_left (hp' i|>.1) hC.start.le).trans (hΨ i|>.1)),(hΨ i|>.2).trans (congr_fun (hp' i|>.2) _)⟩
end YM.OPE.Arboreal.Arcade
