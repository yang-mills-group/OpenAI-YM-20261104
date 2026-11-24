import YM.RG05Readout.Records.Gust
/-!
# Actual census from ONE-ROOT packet functions with orientations

At each root takes V coordinates in base orientation (even if crossing
other marker probes). Keep all body functions along eigen paths; the goods
are still at N. Definition by stencil pull, not by m's effective density. Can
be sold even on unanchored parent crops; see Billing separately. Later extract
uniform rates AFTER checking all replicas by same C.balance.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Records
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}{V: ℕ→Type}[∀ i,DecidableEq (V i)][∀ i,Fintype (V i)] {W:Type*}
    {j b k g:ℕ}
set_option quotPrecheck false
local notation "Θ"=> C.S.toDepth
local notation "K"=> C.path.levels.clock.op
local notation "y!"=> Goods G (C.side N p)
local notation "t!" => (1,false)
local notation "R₀"=> C.path.rep N p N
section
lemma like_embed (x:Site (C.side N p)): (C.S.toDepth (le_refl N) p).embed x=x:= by
    let u:=(Θ (le_refl N) p); have he : u.count.val=1:= Nat.eq_of_mul_eq_mul_left (C.S.side N p).property (u.exact_size.symm.trans (Nat.mul_one _).symm)
    change u.embed _=_; rw [Ratio.embed,he,one_smul,Lattice.wrap_lift]
lemma pole {n f:Side}(r:Ratio n f)(x:Signed)(w y:Site n): r.embed (affine x w y)=affine x (r.embed w) (r.embed y):=by
    unfold affine; rw [show r.embed (x.act y+w) = _ from r.root.map_add (x.act y) w,Ratio.root_embed,Ratio.root_embed,r.signed]
lemma turn_s (t:Motion)(d:ℕ): Motion.scalar t (budwgt C p i d)=budwgt C p i d:=by unfold Motion.scalar; split; simp [budwgt]; rfl
lemma stair_rot {n f:Side}(r:Ratio n f)(z x:Site n)(t:Motion)(F:Goods G f):
    stepUp t (r.embed z) (stepUp (1,false) (r.embed x) F)=stepUp t (r.embed (affine t.1 z x)) F:= by
    rw [View.step_cycle, pole]; cases t; rename_i y b; cases b<;> simp [MergeProof.twist]
-- orientation of emission step. R.price rooted at h last
lemma rot_scalar {n:Side}(t:Motion)(o:Site n)(x:ℂ)(f:Goods G n): stepUp t o (x • f)=Motion.scalar t x • stepUp t o f:=funext (fun _=>Motion.scalar_mul ..)
lemma rot_sum {n:Side} {W:Type*} (s:Finset W)(t:Motion)(o:Site n)(F:W→Goods G n): stepUp t o (∑ i∈s,F i)= ∑ i∈s, stepUp t o (F i):=by
    funext Y; simp only [stepUp,Finset.sum_apply]; unfold Motion.scalar;split
    next ht=> exact star_sum ..
    next ht=> rfl
lemma rot_sub {n:Side}(t:Motion)(o:Site n)(f g:Goods G n): stepUp t o (f-g)=stepUp t o f-stepUp t o g:=by funext Y; unfold stepUp Motion.scalar; split; simp_all; rfl

end
section fluct
abbrev Bin (G:Gauge)(n:Side):=Body→Goods G n
abbrev replenishes (C:Family G)(p k N d:ℕ)(hk:k<N)(L:Bin G (C.side N p)): Bin G (C.side N p):=fun f=>
      ∑ i:Address.Bud C p k,budwgt C p k d • stepUp (1,false) ((C.S.toDepth hk p).embed (Address.child C p k i)) (L (Many.headFee C p k i f)) -- hk definition target k+1
-- track not opaque cutoff cap.Keep terminal inside N

def crops (C:Family G)(m p N d:ℕ)(hm:m ≤ N) (L:Bin G (C.side N p))(i)(hi:i ≤ m):Bin G (C.side N p):= Nat.decreasingInduction (motive:=fun _ _=>Bin G (C.side N p)) (fun k hk f=>replenishes C p k N d (hk.trans_le hm) f) L hi
variable (L:Bin G (C.side N p))(hm:m≤ N)
local notation "f!"=> crops C m p N d hm L
lemma crops_step (he:i < m) : f! i he.le=replenishes C p i N d (he.trans_le hm) (f! (i+1) he):=Nat.decreasingInduction_succ_left ..
lemma crops_head : f! m le_rfl=L:= Nat.decreasingInduction_self ..

def uniform (C:Family G)(m p N d:ℕ)(hm:m≤N) (L: Bin G (C.side N p))(i:ℕ)(x:Site (C.side i p))(t:Motion)(f:Body): Goods G (C.side N p):= if h:i ≤ m then stepUp t ((C.S.toDepth (h.trans hm) p).embed x) (crops C m p N d hm L i h f) else 0
variable (A:Planner C p n V W) (s:W→ℕ) (U:W→ Bin G (C.side N p))(F:∀ i,V i→Body)

def swell (i:ℕ)(j:V i):= uniform C m p N (s (A.labelY i j)) hm (U (A.labelY i j)) i (A.supportX i j) (A.motion (A.labelY i j)) (F i j)
local notation "I!"=> swell hm A s U F
variable {F}
lemma pillar (ht:n≤ i)(hv:i < m) (he:∀ k:V (i+1), F (i+1) k=headFee C p i (A.narrows i ht k).2 (F i (A.narrows i ht k).1)) : I! i=windstep A s ht (I! (i+1)):=by
    funext j; unfold windstep Many.combine; let t:= A.narrows i ht
    rw [← Equiv.sum_comp t.symm]; change _=∑ x:V i×Address.Bud C p i, (if (t (t.symm x)).1=j then budwgt C p i (s (A.labelY i (t (t.symm x)).1)) else 0) • ((I! (i+1)) (t.symm x)); simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
    rw [sum_eq_single j]; rotate_left; · intro k _ hp; simp [hp]
    · simp
    let e:=(Θ (hv.trans_le hm) p); let l:= A.motion (A.labelY i j); let Ω:=(K i p).ratio; let f:= A.supportX i j; let g:=(Θ (hv.le.trans hm) p).embed f; let d':=s (A.labelY i j)
    unfold swell uniform; rw [dif_pos hv.le,crops_step ..]; unfold replenishes; rw [rot_sum]; refine sum_congr rfl (fun k _=> ?_)
    rw [if_pos rfl, rot_scalar (G:=G),turn_s, dif_pos (show i+1 ≤ m from hv),he,A.future i ht,A.loyal i ht,show A.narrows i ht (t.symm (j,k))=(j,k) from Equiv.apply_symm_apply ..]
    apply congr_arg (budwgt C p i d' • ·); rw [embed_comp Ω e]; exact stair_rot ..
-- later norms

def precinct (C:Family G)(p N d:ℕ)(v:Palette C d): Bin G (C.side N p):= fun f=> entrance C d N p v 0 f
abbrev clinic (C:Family G)(p N d:ℕ)(v:Palette C d)(i:ℕ)(x:Site (C.side i p))(t:Motion)(f:Body):= uniform C N p N d le_rfl (precinct C p N d v) i x t f
local notation "U'!"=>stepUp
omit [∀ i, DecidableEq (V i)] [∀ i,Fintype (V i)] in
lemma staples (F:∀ i,V i→Body)(v:(j:W)→Palette C (s j))(j:V N):
    swell (le_refl N) A s (fun j=> precinct C p N (s j) (v j)) F N j= stepUp (A.motion (A.labelY N j)) (A.supportX N j) (entrance C (s (A.labelY N j)) N p (v (A.labelY N j)) 0 (F N j)):=by unfold swell uniform; rw [dif_pos le_rfl,crops_head,like_embed]; rfl

lemma gust_spin (f:y!)(t:Motion)(hf: Integrable f (prior G _))(o:Site (C.side m p)): stepUp t o (gust C.path N p N f m hm) = gust C.path N p N (stepUp t ((C.S.toDepth hm p).embed o) f) m hm:=by
    induction hm using Nat.decreasingInduction with
    | self=> rw [gust_base,gust_base,like_embed]
    | of_succ i hi ih=>
         let u:= (K i p).ratio; let b:= u.embed o
         rw [embed_comp u (Θ hi p) _,gust_step _ _ _ _ _ hi,gust_step _ _ _ _ _ hi,← ih b]
         have he:=unison t C.path i N p 0 o (gust C.path N p N f (i+1) hi) (gust_live _ _ _ _ _ hf hi); simp only [blast,pow_zero,one_smul] at he; exact he.symm
lemma pushpart {I:Type}[DecidableEq I]{B:Census I}(Y:Config G (C.side N p)→Poly B)(b:B.Mode)(ht:Integrable Y (prior G _)): (fun U=>(gust C.path N p N Y m hm U).part b)=gust C.path N p N (fun U=>(Y U).part b) m hm:=by -- generalize
    induction hm using Nat.decreasingInduction with
    | self=> rw [gust_base]; simp_rw [gust_base]
    | of_succ i hi ih=> simp_rw [gust_step _ _ _ _ _ hi]; exact (push_get (C.path.levels.transition_mass ..) (gust_live C.path N p N _ ht hi) b).trans (by rw [ih])
end fluct
end YM.RG05Readout.Records
