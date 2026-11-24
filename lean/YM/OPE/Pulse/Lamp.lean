import YM.OPE.Pulse.Thru
/-!
# Interface carrying all prescribed mark paths without burdening the push
with how they want to spend their remaining radius reserves. Adapted from
Replicas/{Lichen,Thunder}. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Patrol
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V I J : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
  [Fintype J][DecidableEq J]{G:Gauge}{n:Side}
structure Lamp (G:Gauge) (n:Side) where
   watch : Config G n→ℂ
   sparks : ℕ→ Config G n→ℂ
   lit : Dominated sparks
namespace Lamp
instance : Inhabited (Lamp G n):=⟨⟨0,0,pawn0⟩⟩
variable (R:Rep G n) (a:Lamp G n)
def rays:= profile R.activities a.sparks
def disburse:= coin R a.watch a.sparks
def Flex (o:Site n)(t:ℝ) := Blade R o a.watch (rays R a) 0 t
end Lamp
variable (A:History G)(N p:ℕ){k i j:ℕ}{H l:ℕ}
    {δ φ σ χ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (A.rep N p (m+1)) (A.rep N p m)}
set_option quotPrecheck false
local notation "R*" => A.rep N p
local notation "Y" => A.levels.budget
local notation "a" => scurry A.levels r χ (δ i) i
local notation "e" => (Y i).supportExponent
local notation "Γ" => (Y i).B
local notation "f" => A.S.side (i+1) p
local notation "c" => A.S.side i p
local notation "Σ'" => (A.levels.clock.op i p)
local notation "Q" => Names V I
structure Brigade (n:Side)(V: Type) where
   head : V
   spin : V→ Motion
   roll : V → Equiv.Perm V
   moves i : i≠head → roll i head=i
   center : V→ Site n
namespace Brigade
variable (P:Brigade n V)
/-- roll to fine step with the same hands -/
def climb (P: Brigade (A.S.side i p) V) : Brigade (A.S.side (i+1) p) V:=⟨P.head,P.spin,P.roll,P.moves, (Σ').ratio.embed ∘ P.center⟩
/-- layout taking from master clock -/
def place (o:I→Site n)(i:V×I): Site n:= if i.1=P.head then o i.2 else affine (P.spin i.1).1 (P.center i.1) (o i.2)
/-- grant views to copies using migration/canonical symmetry -/
def calls (g:I→ Config G n→ℂ)(i:V×I):=if i.1=P.head then g i.2 else stepUp (P.spin i.1) (P.center i.1) (g i.2)
def quotes (u:I→ℂ)(i:V×I):= if i.1=P.head then u i.2 else scalar (P.spin i.1) (u i.2)
variable {R₀:Rep G n}
lemma may (g:I→ Config G n→ℂ)(h:I→ Res G n)(u:I→ℂ) : May P.head P.spin P.center P.roll (P.calls g) (fun i:V×I=> if i.1=P.head then h i.2 else floatUp (P.spin i.1) (P.center i.1) (h i.2)) (P.quotes u):=fun i hi=> ⟨P.moves i hi,fun j=> by simp [hi,calls,quotes]⟩
omit [Fintype I] [DecidableEq I] [Fintype V] in
lemma pointed (o:I→Site n)(i:V)(h:i≠P.head)(j:I): P.place o (i,j)=affine (P.spin i).1 (P.center i) (P.place o (P.head,j)):= by simp [place,h]
omit [Fintype I] [DecidableEq I] [Fintype V] in
lemma pegs (P:Brigade (A.S.side i p) V)(o:I→Site (A.S.side (i+1) p)) : (Σ').ratio.parent ∘ ((P.climb A p).place o)= P.place ((Σ').ratio.parent ∘ o):=by
    funext j; unfold place climb; dsimp only [Function.comp_apply]; split; rfl; exact Push.Local.parent_affine _ (A.S.block_odd _) _ _ _
def lamp (X:I→Lamp G n) := P.calls (fun i=>(X i).watch)
-- contains no h.selected decisions in output statement, for convenience
def ray (R₀:Rep G n)(X:I→Lamp G n) (j:V×I) := if j.fst=P.head then (X j.2).rays R₀ else floatUp (P.spin j.1) (P.center j.1) ((X j.2).rays R₀)
lemma candle (P:Brigade (A.S.side i p) V) (T:I→Lamp G (A.S.side i p)) (h:A.Selected)(he:i≤N): ∃ K:V×I→ℕ→ Config G (A.S.side i p)→ℂ, (∀ i,Dominated (K i)) ∧ (∀ j:V×I, profile (A.rep N p i).activities (K j)=P.ray (A.rep N p i) T j) ∧ (∀ i:I, K (P.head,i)=(T i).sparks):=by -- notation shadow i.
    let ε(j:V):= ((h.represents N p i he).good.labels.moves (P.spin j).1 (P.center j)).some
    let K (j:V×I):= if j.fst=P.head then (T j.2).sparks else fun i=>stepUp (P.spin j.1) (P.center j.1) ((T j.2).sparks ((ε j.1).kp.symm i))
    refine ⟨K,fun j=>?_,fun j=>?_,fun _=> if_pos rfl⟩
    · unfold K; split; exact (T _).lit; exact conduits _ _ _ (T _|>.lit) (ε j.1)
    unfold K ray; split; rfl; apply roam _ _ (ε j.1); intro i U;simp
lemma lamp_eq {P:Brigade n V}{g:V×I → Config G n→ℂ}{u:V×I→ Res G n}{v:V×I→ℂ}(h: May P.head P.spin P.center P.roll g u v)(z:I→Lamp G n)(hf:∀ i,g (P.head,i)=(z i).watch) (hx:∀ i,u (P.head,i)=(z i).rays R₀): g=P.lamp z ∧ u=P.ray R₀ z:= by
   refine ⟨funext fun j=>?_,funext fun j=>?_⟩
   · rcases j with ⟨i,j⟩; by_cases he:i=P.head; subst i; rw [hf]; simp [lamp,calls]; rw [((h i he).2 j).1,hf]; simp [lamp,calls,he]
   rcases j with ⟨i,j⟩; by_cases he:i=P.head; subst i; rw [hx]; simp [ray]; rw [((h i he).2 j).2.1,hx]; simp [ray,he]
end Brigade
structure Fleet (P:Brigade n V)(R:Rep G n)(q:Config G n→Poly (Names V I))(o:I→Site n)(X:I→Lamp G n)(w:I→ℝ): Prop where
    sem : Serves R (P.lamp X) (P.ray R X) q P.head P.spin P.center P.roll (P.place o) (w ∘ Prod.snd) (R.p.supportExponent-3) 1
    pay : Integrable q (prior G _)
    secure i: 0<w i
namespace Fleet
variable {P:Brigade n V}{R₀:Rep G n}{q:Config G n→Poly (Names V I)}{o:I→Site n}{X:I→Lamp G n}{w w':I→ℝ}
lemma shrink (h : Fleet P R₀ q o X w) (hp : ∀ i,0<w' i) (hf : w'≤ w) : Fleet P R₀ q o X w':=by
    have hs i:0<(w ∘ Prod.snd) (i:V×I):= h.secure i.2; have ht i:0<(w' ∘ Prod.snd) (i:V×I):=hp i.2; exact ⟨h.sem.prune hs ht (slighter hs ht (fun i=> (hf i.2).trans_eq (one_mul _|>.symm)) zero_le_one le_rfl) zero_le_one (by simp) (by norm_num), h.pay, hp⟩
end Fleet
local notation "T" => (R* i)
local notation "Z" => (R* (i+1))
structure Debt (D:GaugeDoor (A.rep N p (i+1)) (A.rep N p i)) (w:ℝ)(o:Site f)(F:Lamp G f)(F':Lamp G c): Prop where
    votes : ∃ (m: Set Wing) (u:ℂ) (l t:ℝ), m.Finite ∧ Tale m o ((Σ').ratio.parent o) 1 F.watch (F.rays Z) (F'.rays T) u l t D ∧ 2*w*l≤1 ∧ w*t≤1 ∧ w*‖u‖≤1
    arrives : F'.disburse T= (Σ').push ((Z).beta) (F.disburse Z)
namespace Debt
-- nonneg may follow from t. DON'T require when lowering weight
lemma less {x w w':ℝ} (ht:w*x≤1)(hf:0<w')(hq:w' ≤ w) : w'*x≤1 := by rcases le_total x 0 with hh|hh; exact (mul_nonpos_of_nonneg_of_nonpos hf.le hh).trans zero_le_one; exact (mul_le_mul_of_nonneg_right hq hh).trans ht
variable {A N p} {R:GaugeDoor (A.rep N p (i+1)) (A.rep N p i)} {w w':ℝ}{o:Site (A.S.side (i+1) p)}{F:Lamp G (A.S.side (i+1) p)}{F':Lamp G (A.S.side i p)}
lemma lower (h: Debt A N p R w o F F')(ht:0<w')(hc:w'≤ w) : Debt A N p R w' o F F':=by
   obtain ⟨m,u,l,t,hm,hh,hz,hP,hQ⟩:= h.votes; exact ⟨⟨m,u,l,t,hm,hh,less hz (by positivity) (by gcongr),less hP ht hc,less hQ ht hc⟩, h.arrives⟩
end Debt
end YM.MergeProof.Ribbons.ManyCopies.Patrol
