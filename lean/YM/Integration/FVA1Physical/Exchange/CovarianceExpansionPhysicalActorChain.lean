import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionCutRosterConnected

/-! On the actual field every nonzero mixed hard cofactor requires a chain
of overlapping, active physical supports joining any two of its roots.
The chain may include unmarked vacuum actors. Each actor has a genuine
failed plaquette and its physical range is bounded by its actual cover. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset Lattice RG Wilson Marker Multi Extra.Trajectories Push.AbsoluteSums.Animals
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]{C:Census V}

def Edge (B:Activities G n)(K:ℕ→Poly C)(x y:Site n):Prop:=
  ∃i,K i≠0 ∧ x∈(B.forced i).support ∧ y∈(B.forced i).support

/-- Uses the spatial cut consisting of the whole actual support component
of the first root. Allows every global flag and the full physical denominator. -/
theorem original_mark_chain (B:Activities G n)(p:BudgetPoint)(U:Config G n)(K:ℕ→Poly C)
    (o:V→Site n)(carry:∀(i:ℕ)(r:C.Mode),(K i).part r≠0 → ∀v∈r.val,o v∈(B.forced i).support)
    (K₀:∀i,(K i).part C.quiet=(B.K i U:ℂ))(live:B.gas p U≠0)
    (w:V→ℝ)(wp:∀v,0<w v)(stock:Summable fun i=>Poly.price w (K i))
    (s:C.Mode)(present:(connected (((B.gas p U:ℂ)⁻¹) • ∑'S,RoseRoster.roster B p U K S)).part s≠0)
    (a b:V)(usedA:a∈s.val)(usedB:b∈s.val):
    Relation.ReflTransGen (Edge B K) (o a) (o b):=by
  by_contra apart
  let D:Support n:=univ.filter (fun y=>Relation.ReflTransGen (Edge B K) (o a) y)
  have left:o a∈D:=mem_filter.mpr ⟨mem_univ _,Relation.ReflTransGen.refl⟩
  have right:o b∉D:=fun hb=>apart (mem_filter.mp hb).2
  have cut (i:ℕ)(nz:K i≠0)(away:¬lies B D i):Disjoint (B.forced i).support D:=by
    apply disjoint_left.mpr
    intro x xi xd
    apply away
    intro y yi
    have reach:Relation.ReflTransGen (Edge B K) (o a) x:=(mem_filter.mp xd).2
    exact mem_filter.mpr ⟨mem_univ _,reach.tail ⟨i,nz,xi,yi⟩⟩
  exact present (original_mixed_vanishes B p U K D cut o carry K₀ live w wp stock
    s a b usedA usedB left right)

inductive Walk (B:Activities G n)(K:ℕ→Poly C)(x:Site n):List ℕ→Site n→Prop where
  | stop : Walk B K x [] x
  | step {L:List ℕ}{u v:Site n} (prior:Walk B K x L u)(i:ℕ)(active:K i≠0)
      (before:u∈(B.forced i).support)(after:v∈(B.forced i).support):
    Walk B K x (i::L) v

omit [Fintype V] in
private theorem priced_walk (B:Activities G n)(p:BudgetPoint)(U:Config G n)(K:ℕ→Poly C)
    (licensed:∀i,K i≠0 → (B.forced i).eligible p.threshold U)(x y:Site n)
    (h:Relation.ReflTransGen (Edge B K) x y):
    ∃L:List ℕ,Walk B K x L y ∧
      (∀i∈L,K i≠0 ∧ ∃z∈(B.forced i).inventory,z∈flags p.threshold U) ∧
      separation x y≤(L.map (fun i=>coverNumber p.B (B.forced i).support*(4*p.B+2)+2*p.B)).sum:=by
  induction h with
  | refl =>
    exact ⟨[],.stop,by simp,by simp⟩
  | @tail u v prior step ih =>
    obtain ⟨L,walk,used,fee⟩:=ih
    obtain ⟨i,active,ui,vi⟩:=step
    obtain ⟨z,zi⟩:=(B.forced i).inventory_ne
    have zflag:z∈flags p.threshold U:=(mem_inter.mp ((licensed i active).1.symm ▸ zi :
      z∈(B.forced i).support∩flags p.threshold U)).2
    refine ⟨i::L,walk.step i active ui vi,?_,?_⟩
    · intro k hk
      rcases List.mem_cons.mp hk with hi|hl
      · subst k
        exact ⟨active,z,zi,zflag⟩
      exact used k hl
    have diameter:=Corona.extent (B.forced i).support p.B ui vi
    have triangle:=separation_triangle x u v
    simp only [List.map_cons,List.sum_cons]
    omega

/-- In particular the distance through the original regulator is paid by the
sum of actual physical covers along a specific ordered walk. The list records
the last actor first. No independence of its flags or its operators is assumed. -/
theorem original_failed_walk (B:Activities G n)(p:BudgetPoint)(U:Config G n)(K:ℕ→Poly C)
    (o:V→Site n)(carry:∀(i:ℕ)(r:C.Mode),(K i).part r≠0 → ∀v∈r.val,o v∈(B.forced i).support)
    (licensed:∀i,K i≠0 → (B.forced i).eligible p.threshold U)
    (K₀:∀i,(K i).part C.quiet=(B.K i U:ℂ))(live:B.gas p U≠0)
    (w:V→ℝ)(wp:∀v,0<w v)(stock:Summable fun i=>Poly.price w (K i))
    (s:C.Mode)(present:(connected (((B.gas p U:ℂ)⁻¹) • ∑'S,RoseRoster.roster B p U K S)).part s≠0)
    (a b:V)(usedA:a∈s.val)(usedB:b∈s.val):
    ∃L:List ℕ,Walk B K (o a) L (o b) ∧
      (∀i∈L,K i≠0 ∧ ∃z∈(B.forced i).inventory,z∈flags p.threshold U) ∧
      separation (o a) (o b)≤(L.map (fun i=>coverNumber p.B (B.forced i).support*(4*p.B+2)+2*p.B)).sum:=
  priced_walk B p U K licensed _ _ (original_mark_chain B p U K o carry K₀ live w wp stock s present a b usedA usedB)

end YM.Integration.FVA1Physical.Exchange.RoseCut
