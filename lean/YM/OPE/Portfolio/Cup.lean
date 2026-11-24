import YM.OPE.Backup.Gather
import YM.OPE.Backup.Elaborate
/-! # Native-scale portfolio at individual anchor sites -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Cadet
open Function Filter Finset Lattice RG Wilson Pressure MeasureTheory
open Push Marker Accent Menu Extra.Multi Extra.Trajectories Ribbon Source Local
open Extra.Histories PhysicalNext.Repeat Lotus GridApprox.Nil OPE.Backup Motion
open Muster MergeProof.Float
open scoped Topology BigOperators Classical
variable {I J V : Type*}{G:Gauge}{n f c:Side}
structure Cup (R:Rep G n) where
    home:Config G n→ℂ
    leaves:Res G n
    rights: ∃ k:ℕ→ Config G n→ℂ,Dominated k ∧ leaves=profile R.activities k
namespace Cup
variable {R:Rep G n}
def chosen (p:Cup R) := p.rights.choose
lemma fitted (p:Cup R) : p.leaves=profile R.activities p.chosen:=p.rights.choose_spec.2
lemma held (p:Cup R) : Dominated p.chosen:=p.rights.choose_spec.1
def book (R:Rep G n)(x:Config G n→ℂ)(k:ℕ→ Config G n→ℂ)(hk:Dominated k): Cup R:= ⟨x,profile R.activities k,k,hk,rfl⟩
@[ext] lemma same {p q:Cup R} (h:p.home=q.home)(hh:p.leaves=q.leaves) : p=q:= by cases p; cases q; congr
def pays (P:Cup R) : Config G n→ℂ:= coin R P.home P.chosen
variable {R':Rep G c}{x a b s t:ℝ}
instance : Zero (Cup R) := ⟨book R 0 0 pawn0⟩
instance : Inhabited (Cup R) := ⟨0⟩
private def add (p q:Cup R) : Cup R := ⟨p.home+q.home,p.leaves+q.leaves,p.chosen+q.chosen,combn p.held q.held,(by rw [p.fitted,q.fitted,prof_add _ p.held q.held])⟩
private def smul (x:ℂ) (p:Cup R): Cup R:= ⟨x • p.home,x • p.leaves,x • p.chosen,rainbow p.held _,p.fitted.symm ▸ (profile_scale ..).symm⟩ -- watch cyc
instance : Add (Cup R) := ⟨add⟩
instance : SMul ℂ (Cup R):= ⟨smul⟩
lemma booked (h:R.activities.Valid R.p a b)(p:Cup R)(f: Config G n→ℂ)(k:ℕ→ Config G n→ℂ)(he:Dominated k) (ht:p=book R f k he): p.pays=coin R f k:= ht ▸ (coin_port R _ (book R f k he|>.held) he (book R f k he|>.fitted).symm h)
@[simp] lemma home_zero : (0:Cup R).home=0:=rfl
@[simp] lemma leaves_zero : (0:Cup R).leaves=0:= by change profile R.activities _=_; funext i U; simp [profile,cram]
@[simp] lemma home_add (p q:Cup R) : (p+q).home=p.home+q.home:=rfl
@[simp] lemma leaves_add (p q:Cup R) : (p+q).leaves=p.leaves+q.leaves:=rfl
@[simp] lemma home_smul (p:Cup R)(x:ℂ) : (x • p).home=x • p.home:=rfl
@[simp] lemma leaves_smul (p:Cup R)(x:ℂ) : (x • p).leaves=x • p.leaves:=rfl
instance : AddCommMonoid (Cup R) :=
  { (inferInstance : Zero (Cup R)), (inferInstance : Add (Cup R)) with
    add_assoc:= fun a b c=> Cup.same (by simp [add_assoc]) (by simp [add_assoc])
    add_zero:=fun a=> Cup.same (by simp) (by simp)
    zero_add:=fun a=> Cup.same (by simp) (by simp)
    add_comm:=fun a b=> Cup.same (by simp [add_comm]) (by simp [add_comm])
    nsmul:= nsmulRec }
lemma summing (p:I→Cup R)(u:Finset I) : (∑ i∈u,p i).home=∑ i∈u,(p i).home:=by
    induction u using Finset.induction_on with
    | empty=>simp
    | @insert i t hi IH=> simp [hi,IH]
lemma summingKey (p:I→Cup R)(u:Finset I) : (∑ i∈u,p i).leaves=∑ i∈u,(p i).leaves:=by
    induction u using Finset.induction_on with
    | empty=>simp
    | @insert i t hi IH=> simp [hi,IH]
lemma upbeat (p:Cup R)(a:Motion)(o:Site n)(K: R.activities.Moves a.1 o) : ∃ k:ℕ→ Config G n→ℂ, Dominated k ∧ floatUp a o p.leaves=profile R.activities k:=by
    let k := p.chosen; let f' i:= stepUp a o (k (K.kp.symm i)); refine ⟨f', conduits _ _ _ p.held K,?_⟩; rw [p.fitted]; exact (roam a o K (fun i U=> by unfold f'; rw [K.kp.symm_apply_apply])).symm
-- charge one edge at root path. Radius decay/growth kept external.
structure Edge (S:StepData c n)(D:GaugeDoor R R')(f:Cup R)(g:Cup R')(o:Site n) (o':Site c)(x:ℂ)(C':ℝ):Prop where
    income: S.push R.beta f.pays=g.pays
    travel: ∃ (l:Set Wing) (s t:ℝ), l.Finite ∧ 2*C'*s≤1 ∧ C'*t ≤1 ∧ C'*‖x‖≤ 1 ∧ Tale l o o' 1 f.home f.leaves g.leaves x s t D
lemma Edge.thin {S:StepData c n}{D:GaugeDoor R R'}{f:Cup R}{g:Cup R'}{o o' ξ}
    (h: Edge S D f g o o' ξ a) (he:0 ≤ b)(hx:b ≤ a): Edge S D f g o o' ξ b:=by
    obtain ⟨l,s,t,hL,hh,hy,hv,hZ⟩:= h.travel; have hE (w C C' :ℝ)(hc:0 ≤ C)(he:C ≤ C')(hh:C'*w≤1) : C*w ≤1:= by
       by_cases ht:0≤w; · exact (mul_le_mul_of_nonneg_right he ht).trans hh
       exact (mul_nonpos_of_nonneg_of_nonpos hc (le_of_lt (lt_of_not_ge ht))).trans zero_le_one
    exact ⟨h.income, l,s,t,hL,hE _ _ _ (by positivity) (by linarith only [hx]) hh,hE _ _ _ he hx hy,hE _ _ _ he hx hv,hZ⟩
-- convert Profiles across θ 
end Cup
end YM.MergeProof.Ribbons.ManyCopies.Cadet
