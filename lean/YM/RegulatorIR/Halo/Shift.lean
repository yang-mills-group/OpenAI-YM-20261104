import YM.RegulatorIR.Halo.Reels

/-!
# Translating soft mark in its own full real coordinates

This is purely permutation of tensors; no derivative or density transport
loss. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Halo
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim Finset PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff
variable {G:Gauge}{X Y B C I:Type}{r k a b s:ℕ}

def onPath (D:Equiv.Perm X)(i:Tuple X r):= D ∘ i

def echo (D:Equiv.Perm X)(T:Packet X r): Packet X r:=fun i=>T (onPath D.symm i)
def Echos (D:Equiv.Perm X)(T S:Packet X r):Prop:=∀ x,S (onPath D x)=T x
lemma echos (D:Equiv.Perm X)(T:Packet X r): Echos D T (echo D T) :=fun x=> congr_arg T (show onPath D.symm (onPath D x)=x from funext fun _=>D.symm_apply_apply _)
lemma backward (D:Equiv.Perm X)(i:Tuple X r):onPath D (onPath D.symm i)=i:= by ext1 j; simp [onPath]
lemma Echos.only {D:Equiv.Perm X}{T S:Packet X r}(h:Echos D T S) : S=echo D T:=by ext1 i; exact ((congr_arg S (backward D i)).symm).trans (h _)
lemma echo_zero {D:Equiv.Perm X}:echo D (0:Packet X r)=0:=rfl
lemma echo_sym {D:Equiv.Perm X}{T:Packet X r}(h:IsSym T):IsSym (echo D T):= fun e x=>h e (onPath D.symm x)
namespace Echos
variable {D:Equiv.Perm X}{K:Layer X X}{V Z T S :Packet X r}
def Level (D:Equiv.Perm X)(K:Layer X X):Prop:=∀ x y,K (D x) (D y)=K x y
variable (H:Level D K)
lemma add (h:Echos D V T)(hh:Echos D Z S):Echos D (V+Z) (T+S):=fun x=>congr_arg₂ (·+·) (h x) (hh x)
lemma times (h:Echos D V T)(t:ℝ): Echos D (t • V) (t • T):=fun x=>congr_arg (t*·) (h x)
lemma sums {V T:I→Packet X r}{s: Finset I}(h:∀ i∈s,Echos D (V i) (T i)): Echos D (∑ i∈s,V i) (∑ i∈s,T i):= by intro x;simp_rw [Finset.sum_apply]; exact sum_congr rfl fun i hi=> h i hi x
lemma sync (h:Echos D T V): Echos D (Packet.symmetry T) (Packet.symmetry V):= by intro i;rw [symmetry_at,symmetry_at];apply congr_arg; exact sum_congr rfl fun _ _=> h _
lemma spliced {U U':Packet X (r+1)}{V V':Packet X (s+1)} (h:Echos D U U')(hh:Echos D V V'): Echos D (splice U V) (splice U' V'):=by
 intro p;unfold splice; rw [← D.tsum_eq ]; apply tsum_congr;intro x; unfold lace; apply congr_arg₂ (·*·)
 · rw [← h (Fin.cons x (cutLeft p))]; congr 1; exact (comp_cons ..).symm
 rw [← hh (Fin.cons x (cutRight p))]; congr 1; exact (comp_cons ..).symm
include H
lemma tracks (h:Echos D T S)(i:Fin r) : Echos D (Packet.ray i T K) (Packet.ray i S K):=by
 intro x; unfold Packet.ray; rw [← D.tsum_eq]; apply tsum_congr;intro z; unfold swivel; change K (D (x i)) (D z)*_= _; rw [show K _ _=K _ _ from H (x i) z,← h]; apply congr_arg;apply congr_arg S;ext1 j; by_cases hh:j=i <;> simp [*,onPath]
lemma ferries {T S:Packet X (r+2)}(h:Echos D T S):Echos D (Packet.loop T K) (Packet.loop S K):=by
 intro i; unfold loop; rw [← (Equiv.prodCongr D D).tsum_eq]; apply tsum_congr;intro p; unfold curve;change K (D p.1) (D p.2)*_=_; rw [show K _ _=K _ _ from H p.1 p.2,← h (Tuple.linked i p)]; apply congr_arg; apply congr_arg S;exact (Tuple.map_link ..).symm
lemma fresh (h:Echos D V Z) : Echos D (draft K V) (draft K Z):=by
 apply sync; generalize List.finRange r=l; induction l with
 | nil=>exact h
 | cons a l ih=>exact tracks H ih a
lemma taps {T S U V:Ranked X} {a b} (h:Echos D (T (a+1)) (S (a+1)))(h':Echos D (U (b+1)) (V (b+1))) : Echos D (matchTwo K T U (a+b) (a,b)) (matchTwo K S V (a+b) (a,b)):=by rw [matchTwo, dif_pos rfl,matchTwo,dif_pos rfl]; exact times (sync (spliced h (tracks H h' 0))) _
lemma heat {P:ℕ→Orders X}{V S: Orders X}(h:∀ i e k,Echos D (P i e k) (P i e k))(hh:∀ i k,Echos D (V i k) (S i k)):∀ i k,Echos D (endHeat r K P V i k) (endHeat r K P S i k):=by
 have hP:∀ p i k,Echos D (markHeat K P V p i k) (markHeat K P S p i k):=by
    intro p; induction p using Nat.strong_induction_on with
    | _ p ih=>
       intro i j; cases p
       · rw [markHeat_first,markHeat_first]; exact hh i j
       next p=>
         rw [markHeat_next,markHeat_next];apply times; apply add
         · exact times (sync (ferries H (ih p (by omega) i (j+2)))) _
         unfold drift; apply sums; intro k hk; unfold Diagram.carry; apply sums; intro t ht; unfold force; apply sums; rintro ⟨l,r⟩ hc; rw [← Finset.mem_antidiagonal.mp hc]; exact taps H (ih _ (by have hp:= mem_antidiagonal.mp hk;omega) t.1 (l+1)) (h _ _ _)
 intro i k; unfold endHeat heated; apply sums; exact fun _ _=> hP _ _ _
end Echos

lemma excess (D:Equiv.Perm X)(W: Equiv.Perm Y)(T:Packet X r): Echos (Equiv.sumCongr D W) (offer (Function.Embedding.inl) T) (offer Function.Embedding.inl (echo D T)):=by
 intro i;let E:= Equiv.sumCongr D W;let f:X↪ X⊕Y:=Function.Embedding.inl
 change offer f _ _= offer f _ _; by_cases h:i∈Set.range (acrossT (r:=r) f)
 · obtain ⟨j,rfl⟩:=h;rw [show onPath E (acrossT f j)=acrossT f (onPath D j) from rfl,offer_eq,offer_eq]; exact echos ..
 rw [offer_zero f h, offer_zero]; rintro ⟨j,hj⟩;apply h; refine ⟨onPath D.symm j,?_⟩
 calc
    _=onPath E.symm (acrossT f j):=rfl
    _=i:= by rw [hj]; exact backward E.symm i

-- self-shift logarithms when using true primitive Layer data
section Torus
variable {P:ℝ}{A:Deck P X B}{F:Deck P Y C} (L:GridStep A F)
variable {V T:Orders X}{f:Cover}
lemma step_echo (H:∀ i j,(Step.combine A F).Ready (L.jVac V i j))(hp: Layer.Sym (Step.combine A F) (Step.combine A F) L.line)(hd:Layer.Sym (Step.combine A F) (Step.combine A F) L.driftL):
 L.each r V (fun i j=> echo (A.wind (Motion.across f)) (T i j))= fun i j=> echo (F.wind (Motion.across f)) (L.each r V T i j):=by
 let D:=Step.combine A F; let W:=D.wind (Motion.across f)
 let X' i j:=echo (A.wind (Motion.across f)) (T i j)
 ext1 i;ext1 k; apply Echos.only; intro x
 let a:=GridStep.jVac L V; let b:= logHeat L.line a false
 let R:=fun i j=>offer (firstChannel A F).native (X' i j); let S:=fun i j=>offer (firstChannel A F).native (T i j)
 let v:= endHeat r L.line b S;let s:=endHeat r L.line b R
 have hx(p q u):Echos W (b p q u) (b p q u):=by
    have hv:= (D.ready_iff _).mp (Uniform.heat_uses _ _ _ hp (fun i (_:i ≤ q) j=> H i j) false p q u le_rfl) (Motion.across f)
    simpa [Echos,W,onPath,Motion.sign] using hv
 have hv : Echos W (v i k) (s i k):= Echos.heat (hp (Motion.across f)) hx (fun e j=> excess _ _ (T e j)) i k
 let p:=acrossT (lastChannel A F).native x; exact Echos.fresh (hd (Motion.across f)) hv p
end Torus
end YM.RegulatorIR.Halo
