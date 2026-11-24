import YM.OPE.Compatible.Atlas.Night
/-!
# Word sums and grammar. Keep all valuations. Choose frame once for sum expression. Coeff scale factors supplied outside.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Set Filter MeasureTheory FrameRead Lattice RG Boundary EveryPhase
open scoped Topology BigOperators Classical
variable {X V:Type}
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{U: Spec.Final C F S}
inductive Circuit (U:Spec.Final C F S) (X V:Type)
    | base (b:ℂ)
    | one (F:Atom U X V)
    | plus (A B:Circuit U X V)
    | times (A B:Circuit U X V)
namespace Circuit
def atoms : Circuit U X V → Finset (Atom U X V)
   | base _=> ∅
   | one A=> {A}
   | plus A B| times A B=> atoms A ∪ atoms B
def value (i:V)(x:X→ E4) : Circuit U X V →ℂ
   | base z=> z
   | one A=> A.read i x
   | plus A B=> value i x A+value i x B
   | times A B=>value i x A*value i x B
-- no sign cancellations needed for complex estimate only
variable [PartialOrder X][OrderBot X][Fintype X](D:Origin X)(Q:Finset X)
variable {ψ:Filter V}{T:V→ℝ} (s:V→ X→ℝ)
variable (A:Circuit U X V)(H:Tendsto T ψ atTop)(h:ClearTime D Q ψ s)
include h H
lemma budgeting (g:Sight) {c d η ρ M:ℝ}(hc:0<c)(hd:0<d)(he:0<η)(hρ:0<ρ)(hM:∀ i, ‖FrameRead.trail (g.code i)‖ ≤ M)(h0:0 ≤ M)(hp:(Fintype.card (Wing D Q):ℝ)*(M*ρ) ≤ c/2*η):
   ∃ v:ℝ, ∀ᶠ i in ψ,∀ x:X→E4, (∀ a∈A.atoms, a.Quota D Q (s i) i x η (Real.exp (-d*T i)) ∧ a.Designed i x g c)→ ∀ f:Wing D Q→ℝ,(∀ i,|f i| ≤ ρ) → ∀ w:Wing D Q, Shines ρ (Real.exp (v*T i)) (fun t=> A.value i (reload D Q (s i) g x (Function.update f w t))) :=by
   induction A with
   | base z=>
       refine ⟨1,?_⟩; filter_upwards [(Real.tendsto_exp_atTop.comp H).eventually_ge_atTop ‖z‖] with i hi x _ f hf w; exact ⟨fun _=>z,differentiableOn_const _,fun _ _=>rfl,fun _ _=> by rw [one_mul]; exact hi⟩
   | one a=> obtain ⟨v,hv⟩:=passes D Q s a g H h hc hd he hρ hM h0 hp; refine ⟨v,?_⟩; filter_upwards [hv] with i hi x hx f hf w; obtain ⟨ht,hg⟩:=hx a (Finset.mem_singleton_self _); exact hi x ht hg f hf w
   | plus a b hu hv=>
       obtain ⟨m,hm⟩:= hu; obtain ⟨n,hn⟩:=hv; let q:=max m n; have he:= (RateLE.exp m H|>.addMax (RateLE.exp n H) H) (q+1) (lt_add_one q)
       refine ⟨q+1,?_⟩; filter_upwards [hm,hn,he] with i h h' hc x hx f hf w
       exact Shines.lift (Shines.plus (h x (fun a ha=> hx a (Finset.mem_union_left _ ha)) f hf w) (h' x (fun b hb=> hx b (Finset.mem_union_right _ hb)) f hf w)) ((Real.le_norm_self _).trans hc)
   | times a b hu hv=>
       obtain ⟨m,hm⟩:= hu; obtain ⟨n,hn⟩:=hv; refine ⟨m+n,?_⟩; filter_upwards [hm,hn] with i h h' x hx f hf w; rw [add_mul,Real.exp_add]; exact Shines.times (h x (fun a ha=> hx a (Finset.mem_union_left _ ha)) f hf w) (h' x (fun b hb=> hx b (Finset.mem_union_right _ hb)) f hf w)
omit h H
-- uniform universal axis frame bundle for all potential base configurations
lemma branchable : ∃ I:Finset Sight,∃ b:ℝ,0<b∧∀ i (x:X→E4),∀ t η:ℝ, 0<t→ (∀ a∈A.atoms,a.Quota D Q (s i) i x η t) → ∃ g∈I,∀ a∈A.atoms,a.Designed i x g b:=by
    let F:= fun a : A.atoms=> ({p:Fin a.val.n × Fin a.val.n // p.1≠p.2})
    obtain ⟨J,c,hc,hY⟩:= FrameRead.menu (Sigma F); refine ⟨J,c,hc,fun i x t η ht hP=>?_⟩
    let w(u:Sigma F):= u.1.val.weight i x u.2.val.1 u.2.val.2
    obtain ⟨g,hg,h⟩:= hY w (fun j=> norm_pos_iff.mp (ht.trans_le ((hP j.fst.val j.fst.2).split j.2.val.1 j.2.val.2 j.2.2)))
    exact ⟨g,hg,fun a ha=>⟨fun u v hp j=> h ⟨⟨a,ha⟩,⟨(u,v),hp⟩⟩ j⟩⟩
end Circuit
end YM.OPE.Arboreal.Trace
