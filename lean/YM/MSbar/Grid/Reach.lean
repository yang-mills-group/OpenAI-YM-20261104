import YM.MSbar.Grid.Carries

/-! Evaluate approximation on any prescribed moment kernel, including unbalanced demand and
all permutations. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Loops
open Function Finsupp Super Finset Filter Set MeasureTheory
open scoped BigOperators Classical Topology
variable {C M:Type*} [AddCommGroup M] [MeasurableSpace M] [TopologicalSpace M] {μ:Measure M} {B:Snap M μ}
  {I:Finset C} {F G: ℕ→Amps C M}{f g:Amps C M}{k : Bit}{p : C→Bit} [IsTopologicalAddGroup M] [T2Space M]
-- all momenta; for any natural n.
def catalogue (n:ℕ)(a:Fin n→C)(p:Fin n→M):Field C M:= List.ofFn fun i=>(a i,p i)
def Arc (f:Amps C M) :=∀ (n:ℕ)(a:Fin n→C),ContinuousOn (fun x:Fin n→M=> f (catalogue n a x)) {x | channel (catalogue n a x)=0}
lemma Arc.copies (h:Arc f)(hf:Quiet f):Copies B.clan (fun _=>f) f:=by
    refine ⟨fun _=>hf,hf,fun w he u hv=>?_⟩; let L:=Fin u.length; let p(i:L):= (u.get i).1; let G(i:L):=(u.get i).2; let V(n)(i:L):=(G i).f n; let q (i:L):=(G i).target
    have h1:u.cap=catalogue _ p q:= by unfold Deck.cap catalogue; exact (List.ofFn_getElem_eq_map u (fun x:C × Ticket B.clan w=>(x.1,x.2.target))).symm
    have h2(n):u.see n=catalogue _ p (V n):=by unfold Deck.see catalogue; exact (List.ofFn_getElem_eq_map u (fun x:C × Ticket B.clan w=>(x.1,x.2.f n))).symm
    have hp:channel (catalogue _ p q)=0:=by rw [← h1]; exact u.report hv
    simp_rw [h1,h2]; exact (h _ p q hp).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨tendsto_pi_nhds.mpr (fun i=>(G i).tend),Eventually.of_forall fun i=>by change channel (catalogue _ _ _)=_; rw [← h2]; exact hv i⟩)

namespace Deck
omit [MeasurableSpace M] [IsTopologicalAddGroup M] [T2Space M] in
private lemma decomposed {K : ℕ → AddSubgroup M}{v:Deck C K id} {x y} (hv : Deck.cap v=x++y) : ∃ a b: Deck C K id,a.cap=x∧b.cap=y∧a++b=v:=by
    induction x generalizing v with
    | nil => exact ⟨[],v,rfl,(by simpa using hv),rfl⟩
    | cons p x ih =>
       cases v with
       | nil => simp [cap] at hv
       | cons a v =>
          rw [show cap (a::v)= (a.1,a.2.target)::Deck.cap v from rfl, List.cons_append,List.cons.injEq] at hv
          obtain ⟨u,b,h,h',rfl⟩:= ih hv.2; exact ⟨a::u,b,by change _::u.cap=_; rw [show Deck.cap u=x from h]; exact congr_arg (·::x) hv.1,h',rfl⟩
private lemma harmony (r : Bit) (p : C→Bit)(u v: Deck C B.clan id)(x y:C×Ticket B.clan id)
   (hf:Copies B.clan F f)(hh:∀ i,Homogeneous (lift p) r (F i))(he:∀ n,channel (Deck.see (u++x::y::v) n)=0):
    f (u.cap++(x.1,x.2.target)::(y.1,y.2.target)::v.cap)= sign (p x.1) (p y.1)* f (u.cap++(y.1,y.2.target)::(x.1,x.2.target)::v.cap) := by
   let w := u++x::y::v; let w' :=u++y::x::v; have hz : w.Perm w':= (List.Perm.swap ..).append_left u
   have ht:=hf.pilots id tendsto_id w he
   have he':=hf.pilots id tendsto_id w' (fun n=>(channel_move ((hz.map (fun x:C× Ticket B.clan id=>(x.1,x.2.f n))).symm)).trans (he n))
   simp_rw [w,see,cap,List.map_append,List.map_cons,id] at ht; simp_rw [w',see,cap,List.map_append,List.map_cons,id] at he'; exact tendsto_nhds_unique ht ((he'.const_mul (sign (p x.1) (p y.1))).congr' (Eventually.of_forall fun i=> Eq.symm ((hh i).commute _ _ _ _)))
end Deck
lemma Copies.homogeneous (hf:Copies B.clan F f)(hh:∀ i,Homogeneous (lift p) k (F i)):Homogeneous (lift p) k f:=by
   constructor
   · intro u x y v
     by_cases hr:channel (u++x::y::v)=0; swap
     · rw [hf.quiet _ hr,hf.quiet _ (by rw [channel_move ((List.Perm.swap ..).append_left u : (u++y::x::v).Perm (u++x::y::v))]; exact hr),mul_zero]
     obtain ⟨W,hW,h⟩:= B.ships _ tendsto_id hr
     obtain ⟨R,Q,rfl,hQ,rfl⟩:= Deck.decomposed hW; rcases Q with _|⟨a, _|⟨b,v⟩⟩ <;> simp only [Deck.cap,List.map_nil,List.map_cons,List.cons.injEq, reduceCtorEq, and_false] at hQ <;> try contradiction
     obtain ⟨rfl,rfl,rfl⟩:= hQ; exact Deck.harmony k p R v a b hf hh h
   intro v h; by_cases he: channel v=0; swap; exact hf.quiet v he
   obtain ⟨W,rfl,hZ⟩:= B.ships v tendsto_id he
   apply tendsto_nhds_unique (hf.pilots id tendsto_id _ hZ) (tendsto_const_nhds.congr (fun n=>?_))
   exact ((hh n).shape (Deck.see W n) (by simpa [oddity,Deck.see,lift,comp_def,List.map_map, Deck.cap] using h)).symm
end YM.MSbar.Loops
