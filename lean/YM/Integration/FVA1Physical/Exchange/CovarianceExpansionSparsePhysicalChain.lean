import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionPhysicalActorChain

/-! Shorten a physical support path until only consecutive actors can overlap.
Alternating actors then require distinct genuine failed flags. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset Lattice RG Wilson Marker Multi Extra.Trajectories Push.AbsoluteSums.Animals
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]{C:Census V}

def Sparse (B:Activities G n):List ℕ→Prop
  | []=>True
  | i::L=>(∀k∈L.tail,Disjoint (B.forced i).support (B.forced k).support) ∧ Sparse B L

omit [Fintype V] in
private theorem meet (B:Activities G n)(K:ℕ→Poly C){x u:Site n}{L:List ℕ}
    (w:Walk B K x L u)(clean:Sparse B L)(unique:L.Nodup)
    (i:ℕ)(active:K i≠0)(v:Site n)(vi:v∈(B.forced i).support)
    (met:x∈(B.forced i).support ∨ ∃j∈L,¬Disjoint (B.forced j).support (B.forced i).support):
    ∃M,Walk B K x M v ∧ Sparse B M ∧ M.Nodup:=by
  rcases met with xi|hit
  · exact ⟨[i],Walk.step .stop i active xi vi,by simp [Sparse],by simp⟩
  revert clean unique hit
  induction w with
  | stop => simp
  | @step L u y prior j good uj yj ih =>
    intro simple unique hit
    by_cases old:∃k∈L,¬Disjoint (B.forced k).support (B.forced i).support
    · exact ih simple.2 (List.nodup_cons.mp unique).2 old
    have avoided (k:ℕ)(hk:k∈L):Disjoint (B.forced i).support (B.forced k).support:=by
      apply Disjoint.symm
      by_contra h
      exact old ⟨k,hk,h⟩
    have overlap:¬Disjoint (B.forced j).support (B.forced i).support:=by
      obtain ⟨k,hk,hitk⟩:=hit
      rcases List.mem_cons.mp hk with eq|past
      · exact eq ▸ hitk
      exact False.elim (old ⟨k,past,hitk⟩)
    obtain ⟨z,zj,zi⟩:=not_disjoint_iff.mp overlap
    by_cases duplicate:i=j
    · subst i
      exact ⟨j::L,prior.step j good uj vi,simple,unique⟩
    have fresh:i∉L:=fun h=>disjoint_left.mp (avoided i h) vi vi
    refine ⟨i::j::L,(prior.step j good uj zj).step i active zi vi,⟨avoided,simple⟩,?_⟩
    exact List.nodup_cons.mpr ⟨fun h=>(List.mem_cons.mp h).elim duplicate fresh,unique⟩

omit [Fintype V] in
private theorem shorten (B:Activities G n)(K:ℕ→Poly C)(x y:Site n)
    (h:Relation.ReflTransGen (Edge B K) x y):
    ∃L,Walk B K x L y ∧ Sparse B L ∧ L.Nodup:=by
  induction h with
  | refl => exact ⟨[],.stop,True.intro,by simp⟩
  | @tail u v _ step ih =>
    obtain ⟨i,active,ui,vi⟩:=step
    obtain ⟨L,w,clean,unique⟩:=ih
    apply meet B K w clean unique i active v vi
    cases w with
    | stop => exact Or.inl ui
    | @step M a b prev j live aj bj =>
      exact Or.inr ⟨j,List.mem_cons_self,not_disjoint_iff.mpr ⟨_,bj,ui⟩⟩

/-- One and the same nonzero mixed hard cofactor admits a chain with no
repeated physical actor and no overlap between nonadjacent supports. -/
theorem original_sparse_walk (B:Activities G n)(p:BudgetPoint)(U:Config G n)(K:ℕ→Poly C)
    (o:V→Site n)(carry:∀(i:ℕ)(r:C.Mode),(K i).part r≠0 → ∀v∈r.val,o v∈(B.forced i).support)
    (K₀:∀i,(K i).part C.quiet=(B.K i U:ℂ))(live:B.gas p U≠0)
    (w:V→ℝ)(wp:∀v,0<w v)(stock:Summable fun i=>Poly.price w (K i))
    (s:C.Mode)(present:(connected (((B.gas p U:ℂ)⁻¹) • ∑'S,RoseRoster.roster B p U K S)).part s≠0)
    (a b:V)(usedA:a∈s.val)(usedB:b∈s.val):
    ∃L,Walk B K (o a) L (o b) ∧ Sparse B L ∧ L.Nodup:=
  shorten B K _ _ (original_mark_chain B p U K o carry K₀ live w wp stock s present a b usedA usedB)

def alternate : List ℕ→List ℕ
  | []=>[]
  | [i]=>[i]
  | i::_::L=>i::alternate L

private theorem alternate_subset : ∀(L:List ℕ),∀i∈alternate L,i∈L
  | [],_ => by simp [alternate]
  | [_],_ => by simp [alternate]
  | u::v::L,i => by
    intro h
    rcases List.mem_cons.mp h with eq|mem
    · exact List.mem_cons.mpr (Or.inl eq)
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (alternate_subset L i mem))

private theorem alternate_enough : ∀(L:List ℕ),L.length≤2*(alternate L).length
  | [] => by simp [alternate]
  | [_] => by simp [alternate]
  | i::j::L => by
    have cut:=alternate_enough L
    simp only [List.length_cons,alternate]
    omega

private theorem alternate_apart (B:Activities G n):∀(L:List ℕ),Sparse B L →
    (alternate L).Pairwise (fun i j=>Disjoint (B.forced i).support (B.forced j).support)
  | [],_ => by simp [alternate]
  | [_],_ => by simp [alternate]
  | i::j::L,apart => by
    exact List.pairwise_cons.mpr ⟨fun k hk=>apart.1 k (alternate_subset L k hk),
      alternate_apart B L apart.2.2⟩

private theorem count_flags (B:Activities G n)(F:Support n)(L:List ℕ)
    (apart:L.Pairwise fun i j=>Disjoint (B.forced i).support (B.forced j).support)
    (each:∀i∈L,∃z∈(B.forced i).support,z∈F):L.length≤F.card:=by
  induction L generalizing F with
  | nil => simp
  | cons i L ih =>
    obtain ⟨z,zi,zf⟩:=each i List.mem_cons_self
    have rest (j:ℕ)(h:j∈L):∃v∈(B.forced j).support,v∈F.erase z:=by
      obtain ⟨v,vj,vf⟩:=each j (List.mem_cons_of_mem _ h)
      have diff:v≠z:=fun eq=>disjoint_left.mp ((List.pairwise_cons.mp apart).1 j h) zi (eq ▸ vj)
      exact ⟨v,vj,mem_erase.mpr ⟨diff,vf⟩⟩
    have h:=ih (F.erase z) (List.pairwise_cons.mp apart).2 rest
    have card:=card_erase_add_one zf
    simp only [List.length_cons]
    omega

omit [Fintype V] in
theorem walk_active {B:Activities G n}{K:ℕ→Poly C}{x y:Site n}{L:List ℕ}
    (walk:Walk B K x L y):∀i∈L,K i≠0:=by
  induction walk with
  | stop => simp
  | @step M u v h j nz uj vj ih =>
    intro i hi
    rcases List.mem_cons.mp hi with eq|prev
    · exact eq ▸ nz
    exact ih i prev

omit [Fintype V] in
theorem original_many_flags (B:Activities G n)(p:BudgetPoint)(U:Config G n)(K:ℕ→Poly C)
    (licensed:∀i,K i≠0 → (B.forced i).eligible p.threshold U)
    {x y:Site n}{L:List ℕ}(walk:Walk B K x L y)(sparse:Sparse B L)(F:Support n)
    (inside:∀i∈L, (B.forced i).support⊆F):
    L.length≤2*((flags p.threshold U)∩F).card:=by
  have active:=walk_active walk
  have many:=count_flags B (flags p.threshold U∩F) (alternate L) (alternate_apart B L sparse)
  apply (alternate_enough L).trans (Nat.mul_le_mul_left 2 (many ?_))
  intro i hi
  have belongs:=alternate_subset L i hi
  obtain ⟨z,zi⟩:=(B.forced i).inventory_ne
  obtain ⟨zs,zf⟩:=mem_inter.mp ((licensed i (active i belongs)).1.symm ▸ zi :
    z∈(B.forced i).support∩flags p.threshold U)
  exact ⟨z,zs,mem_inter.mpr ⟨zf,inside i belongs zs⟩⟩

end YM.Integration.FVA1Physical.Exchange.RoseCut
