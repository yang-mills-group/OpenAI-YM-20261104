import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionSparsePhysicalChain

/-! A separated signed physical cofactor forces either a large funded actor
meeting a nominated finite ball, or many distinct true failed plaquettes in
that ball. No global bound on the number or placement of other flags enters. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset Lattice RG Wilson Marker Multi Extra.Trajectories Push.AbsoluteSums.Animals
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]{C:Census V}

abbrev width (p:BudgetPoint)(D:ℕ):ℕ:=D*(4*p.B+2)+2*p.B

def LongAt (B:Activities G n)(p:BudgetPoint)(K:ℕ→Poly C)(x:Site n)(k D:ℕ):Prop:=
  ∃i,K i≠0 ∧ D<coverNumber p.B (B.forced i).support ∧
    ∃u∈(B.forced i).support,u∈neighbors (k*width p D) x

omit [Fintype V] in
private theorem head_walk {B:Activities G n}{K:ℕ→Poly C}{x y:Site n}{L:List ℕ}
    (w:Walk B K x L y)(clean:Sparse B L)(k:ℕ)(bound:k≤L.length):
    ∃(Q:List ℕ)(z:Site n),Walk B K x Q z ∧ Sparse B Q ∧ Q.length=k:=by
  revert clean bound
  induction w with
  | stop =>
    intro _ h
    have : k=0:=by simpa using h
    exact ⟨[],x,.stop,True.intro,this.symm⟩
  | @step L u v h i active prevSite lastSite ih =>
    intro good len
    by_cases smaller:k≤L.length
    · exact ih good.2 smaller
    have eq:k=(i::L).length:=by simp only [List.length_cons] at *;omega
    exact ⟨i::L,v,h.step i active prevSite lastSite,good,eq.symm⟩

omit [Fintype V] in
private theorem local_span {B:Activities G n}(p:BudgetPoint){K:ℕ→Poly C}{x y:Site n}{L:List ℕ}
    (w:Walk B K x L y)(k D:ℕ)(short:¬LongAt B p K x k D)(len:L.length≤k):
    separation x y≤L.length*width p D ∧
      ∀i∈L,∀z∈(B.forced i).support,separation x z≤L.length*width p D:=by
  revert len
  induction w with
  | stop => simp
  | @step L u v h i active before after ih =>
    intro len
    have next:L.length+1≤k:=by simpa only [List.length_cons] using len
    have prev:L.length≤k:=by omega
    obtain ⟨near,used⟩:=ih prev
    have inside:u∈neighbors (k*width p D) x:= (neighbors_mem _ _ _).2
      (near.trans (Nat.mul_le_mul_right (width p D) prev))
    have bought:coverNumber p.B (B.forced i).support≤D:=by
      by_contra! tall
      exact short ⟨i,active,tall,u,before,inside⟩
    have reach (z:Site n)(within:z∈(B.forced i).support):separation x z≤(L.length+1)*width p D:=by
      have diam:=Corona.extent (B.forced i).support p.B before within
      have fee:separation u z≤width p D:=diam.trans
        (Nat.add_le_add_right (Nat.mul_le_mul_right (4*p.B+2) bought) (2*p.B))
      calc separation x z≤separation x u+separation u z:=separation_triangle _ _ _
           _≤L.length*width p D+width p D:=Nat.add_le_add near fee
           _=(L.length+1)*width p D:=(Nat.succ_mul ..).symm
    refine ⟨reach _ after,?_⟩
    intro j hj z zj
    rcases List.mem_cons.mp hj with eq|old
    · subst j
      exact reach z zj
    exact (used j old z zj).trans (Nat.mul_le_mul_right _ (Nat.le_succ L.length))

/-- A nonzero connected coefficient between two actual anchors that are farther
apart than k short diameters forces a *local* event. If there is no large
active support touching the nominated ball, at least ceiling(k/2) distinct
original failed plaquettes lie inside that actual torus ball. This remains
true with arbitrary additional exterior marks and compulsory vacuum flags. -/
theorem original_limited_window (B:Activities G n)(p:BudgetPoint)(U:Config G n)(K:ℕ→Poly C)
    (o:V→Site n)(carry:∀(i:ℕ)(r:C.Mode),(K i).part r≠0 → ∀v∈r.val,o v∈(B.forced i).support)
    (licensed:∀i,K i≠0 → (B.forced i).eligible p.threshold U)
    (K₀:∀i,(K i).part C.quiet=(B.K i U:ℂ))(live:B.gas p U≠0)
    (w:V→ℝ)(wp:∀v,0<w v)(stock:Summable fun i=>Poly.price w (K i))
    (s:C.Mode)(present:(connected (((B.gas p U:ℂ)⁻¹) • ∑'S,RoseRoster.roster B p U K S)).part s≠0)
    (a b:V)(usedA:a∈s.val)(usedB:b∈s.val)(k D:ℕ)
    (separated:k*width p D<separation (o a) (o b)):
    LongAt B p K (o a) k D ∨
      k≤2*((flags p.threshold U)∩neighbors (k*width p D) (o a)).card:=by
  by_cases long:LongAt B p K (o a) k D
  · exact Or.inl long
  right
  obtain ⟨L,walk,sparse,_⟩:=original_sparse_walk B p U K o carry K₀ live w wp stock s present a b usedA usedB
  have room:k≤L.length:=by
    by_contra! few
    have near:=(local_span p walk k D long few.le).1
    exact (not_le_of_gt separated) (near.trans (Nat.mul_le_mul_right _ few.le))
  obtain ⟨Q,z,short,apart,len⟩:=head_walk walk sparse k room
  have inside:= (local_span p short k D long len.le).2
  rw [←len]
  apply original_many_flags B p U K licensed short apart
  intro i hi v vi
  exact (neighbors_mem _ _ _).2 (inside i hi v vi)

end YM.Integration.FVA1Physical.Exchange.RoseCut
