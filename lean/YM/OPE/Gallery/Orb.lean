import YM.OPE.Gallery.Ball
/-!
# Cadet segment between BEGIN (j) and LAND (k), both included

Allows roughly witnessed histories within the segment, using power balance in
ratio a_j/a_k. It's important to choose footprint support tolls AT EACH step where
moderate separation would fail at the projection; recording one merger event
that destroys at least one earlier primitive at that step pays for every such
failure again at a later step. No pose that all these marriages have the same support.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Cadet.Lecture
open Function Filter Finset Lattice RG Wilson Pressure MeasureTheory
open Push Marker Accent Menu Extra.Multi Extra.Trajectories Ribbon Source Local
open Extra.Histories PhysicalNext.Repeat Lotus GridApprox.Nil OPE.Backup Motion
open Muster MergeProof.Float Labels Bid Cadet Drapery
open scoped Topology BigOperators Classical
variable {G:Gauge}{I J V L B X : Type}[Fintype V][DecidableEq V]{n:Side}
variable [Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype L][DecidableEq L][Fintype B][DecidableEq B][Fintype X][DecidableEq X]
variable {H:History G}{N p k m i j b T ℓ μ:ℕ}
set_option quotPrecheck false
-- segment is general, often k=m+1 before final Throw; operates j+1→ k across Colon.Start
structure Season (P:Playout H p b N V)(k j:ℕ)(δ ψ φ:ℕ→ℝ)(z:ℕ→ℕ)(η:ℕ→ℝ)(r:ℕ→ℕ)(A:Fibers I J) (s:Finset J) (p':∀ m:ℕ,I→ Site (H.S.side m p)) (s':Ward (Names V J)) (T:ℕ) (W:ℕ→I→ℝ)(α:ℝ) (D:∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m)) (F:∀ m:ℕ,I→ Cup (H.rep N p m)) : Prop where
    store : BudgetStop H D δ ψ φ z η r b
    depth : b ≤ k
    tall : k<j
    bound : j<N
    licence : 0<T
    purchase : Fintype.card I ≤ T
    thaws : 0<α ∧ α≤1
    bare : Trial s'
    rests i: i∈s→ A.Solo i
    roomP i:k ≤ i→ i ≤ j→ ∀ l, p' i l=(H.levels.clock.op i p).ratio.parent (p' (i+1) l)
    group j': k ≤ j' → j' ≤ j → P.occupied (r j') (p' j') ∧ P.occupied (r j') (p' (j'+1))
    space j': k ≤ j'→j' ≤ j→ ∀ x y:V×I,Drapery.room (pullback A s') x y → (partialGroup V A).bunch x ≠ (partialGroup V A).bunch y → let f:=P.spectrum j' (p' j'); (H.levels.budget j').B*z j' ≤ separation (f x) (f y)
    budgets j': k ≤ j'→ ∀ he:j' ≤ j,8*α ≤ η j'* ManyCopies.license H δ T (z j'+2) j' ∧ ManyCopies.license H δ T (z j'+2) j' ≤ 1 ∧ ClusterPars H δ φ r j'∧ Arsenal (H.rep N p j') ∧ MergeProof.Float.Runs (D N p j' (lt_of_le_of_lt he bound)) (H.levels.clock.op j' p) (6*((H.S.block j').val:ℝ)) -- `‹›` not accessible in arrow type without binder
    landing x y : A.bunch x=A.bunch y→p' k x=p' k y
    width i:k ≤ i→ i≤j+1→∀ x,0 < W i x
    payment i:k ≤ i→i ≤ j→ ∀ x, η i*W i x ≤ W (i+1) x
    awake i:k ≤ i→ i < j → ∀ x,A.bunch x∉s→ W i x=W (i+1) x
    readiness i: ∃ ξ:ℂ,Cup.Edge (H.levels.clock.op j p) (D N p j bound) (F (j+1) i) (F j i) (p' (j+1) i) (p' j i) ξ (W (j+1) i)
    staying i: A.bunch i∈s→ Program H N p k (j+1) (fun m=>p' m i) (fun m=>F m i) (fun m=> W m i) D bound

variable {D:∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}
    {δ ψ φ η:ℕ→ℝ}{z r:ℕ→ℕ}{P:Playout H p b N V}{A:Fibers I J}{K:Fibers I L}{C:Fibers L J}
    {α:ℝ}{W:ℕ→I→ℝ}{F:∀ m:ℕ,I→ Cup (H.rep N p m)} {s:Finset J} {s':Ward (Names V J)} {p':∀ m:ℕ,I→ Site (H.S.side m p)}
    (p₀:I→ Config G (H.S.side N p)→ℂ) (U:Season P k j δ ψ φ z η r A s p' s' T W α D F)
local notation "P'"=> (H.levels.budget i)
local notation "L'"=> ( (H.S.block i).val:ℝ)
local notation "S"=> (H.levels.clock.op i p)
local notation "Ξ"=> H.rep N p
local notation "Q"=> (D N p)
local notation "a₀"=> bill H i j (Fintype.card I-Fintype.card L+1) α (W i) K
local notation "a₁"=> bill H (i+1) j (Fintype.card I-Fintype.card L+1) α (W (i+1)) K
-- Burn receipts on awakened unit.During segment maintain pepper=0 for awake.Under use `Blade` budgets.Leg.Surface
structure Hostage (i:ℕ)(hi:i≤N)(K:Fibers I L)(C:Fibers L J) (F':L→ Cup (H.rep N p i))(u:L→ℝ) : Prop where -- other section params inferred? `Season`
    market : P.Market (pullback C s') (p' i∘ K.twig) F' (P.intention (Playout.Rake.grouped_X p₀ K) i hi) u ((H.levels.budget i).supportExponent-3)
    stays l : C.bunch l∈s→ F' l=F i (K.twig l)
    lives l : C.bunch l∉s→ Blade (H.rep N p i) (p' i (K.twig l)) (F' l).home (F' l).leaves 0 (1/(2*u l))

-- Slosh with kept state.Simple `sparks`.Cost ∝ one-block ages.Arc
lemma sloshes {f':Cup (H.rep N p (i+1))} (hk:k ≤ i)(hi:i < j){a w:ℝ}{o:Site (H.S.side (i+1) p)}
    (hf:Blade (Ξ (i+1)) o f'.home f'.leaves 0 (1/(2*w))) (he:0<w)(hw:0<a)(h: a ≤ w / L'^4) : ∃ g:Cup (H.rep N p i), Cup.Edge S (Q i (hi.trans U.bound)) f' g o ((S).ratio.parent o) 0 w ∧ Blade (Ξ i) ((S).ratio.parent o) g.home g.leaves 0 (1/(2*a)) :=by -- type parse
    have hA:= U.store.well; have hM:= hi.trans U.bound; have hL:2 ≤ L':= size_enough H i; let D':=6*L'; have hD: 0 ≤ D':=(by unfold D'; linarith only [hL]); let x:=1/(2*w)
    rw [f'.fitted] at hf
    obtain ⟨f,K,hQ,hμ,hN,hB⟩:= Float.slosh (hf : Blade (Ξ (i+1)) o f'.home (profile (Ξ (i+1)).activities f'.chosen) 0 x) (hA.represents N p _ hM).good f'.held (U.budgets i hk hi.le|>.2.2.2.2) hD (hA.represents N p i hM.le).good.labels (hA.steps N p i hM|>.1.symm) (H.levels.transition_mass ..)
    let P:=Cup.book (Ξ i) f K hμ; obtain ⟨Y,hY,hX⟩:= hN; refine ⟨P,⟨(hB.trans ?_), Y,x,0,hY,by unfold x; field_simp; simp,by simp,by simp,?_⟩,?_⟩ -- hB orientation & q needs `f'.fitted`
    · exact (Cup.booked (hA.represents N p i hM.le|>.good.labels) P _ _ _ rfl).symm
    · rw [f'.fitted]; exact hX
    let L0:= L'; have hP: 0< L0:=zero_lt_two.trans_le hL; have hv:D'*a ≤ w:= by
       have hx:D'≤L0^4:= by change 6*L0≤L0^4; have hh:L0^1=L0:=pow_one _; rw [pow_succ, mul_le_mul_iff_left₀ hP]; norm_num; refine le_trans (b:=(2:ℝ)^3) (by norm_num) (pow_le_pow_left₀ zero_le_two hL _) 
       refine le_trans (mul_le_mul_of_nonneg_right hx hw.le) ((mul_comm (L0^4) a).trans_le ((le_div_iff₀ (pow_pos hP 4)).1 h))
    apply hQ.more; rw [← mul_div_assoc]; exact (div_le_div_iff₀ (by positivity) (by positivity)).2 (by linarith only [hv])

variable (h:splitAt A K C)(hX:∀ i,Continuous (p₀ i))
include h U
lemma near_stay (hr: (¬Spaced (pullback C s') (P.spectrum i (p' i ∘ K.twig)) ((H.levels.budget i).B*z i)))(hk:k ≤ i)(hi:i≤ j): ∃ (J':Type)(_ : Fintype J')(_ : DecidableEq J')(A:Fibers L J')(B:Fibers J' J), splitAt C A B ∧
    (∀ v:L, coverNumber (P').B ({p' i (K.twig (A.twig (A.bunch v))),p' i (K.twig v)}:Support _ ) ≤ z i+2) ∧ Fintype.card J'<Fintype.card L:=by
    let f:= P.spectrum i (p' i); let Δ:= (P').B*z i; let o(v):= p' i (K.twig v); unfold Spaced at hr; push Not at hr; obtain ⟨a,b,hs,hk',hv⟩:=hr; have he: (partialGroup V C).bunch a=(partialGroup V C).bunch b:=not_not.mp (fun hx=> not_lt_of_ge (h.apart (U.space i hk hi) a b hs hx) hv); have hz:a.1=b.1:= (Prod.mk.inj (show (a.1,C.bunch a.2)=(b.1,C.bunch b.2) from he)).1; have hζ: a.2 ≠ b.2:= fun h=>hk' (Prod.ext hz h)
    have hx: separation (o a.2) (o b.2) ≤ Δ:= by unfold Playout.spectrum at hv; rw [hz] at hv; simpa [o,Δ,affine,separation_translate,separation_signed] using hv.le
    obtain ⟨J,cI,cJ,Jk,A,hK,hE,hr⟩:= proposal a.snd b.snd hζ (show C.bunch a.2=C.bunch b.2 from congr_arg Prod.snd he)
    refine ⟨J,cI,cJ,Jk,A,hK,fun v=>?_,hr⟩; rw [hE]; split; next he=> rw [he]; exact OPE.Log.moderateRadius _ _ _ _ hx
    exact OPE.Log.moderateRadius _ _ _ _ (by simp)
-- dawn of one step
end YM.MergeProof.Ribbons.ManyCopies.Cadet.Lecture
