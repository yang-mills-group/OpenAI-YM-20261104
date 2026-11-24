import YM.Integration.FVA1Physical.CommonHull.InteractingShortReachVolume
import YM.Integration.FVA1Physical.CommonHull.InteractingFailedPathGeometry
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionShortTerritory

/-! The charged region is the actual component reached by the original
short active actors, including the complete compulsory scalar actors. Its
expected size is bounded independently of the overall volume and cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Marked.RemoteRoster
open Set Finset MeasureTheory Lattice RG Wilson Marker Multi Extra.Trajectories Push.AbsoluteSums.Animals
open QuadraticLocal QuadraticLocal.Fusion.Attached Exchange Exchange.RoseCut
open private flagGraph Tether advance list_book from YM.Integration.FVA1Physical.CommonHull.InteractingFailedPathGeometry
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]{C:Census V}

private theorem last_walk {F:Support n}{r:ℕ}{a b:↥F}(p:(flagGraph F r).Walk a b)(x:Site n):
    endSite x (p.support.map Subtype.val)=b.1:=by
  induction p generalizing x with
  | nil=>rfl
  | cons _ _ ih=>exact ih _

omit [Fintype V] in
theorem short_territory_witness (B:Activities G n)(p:BudgetPoint)(U:Config G n)(K:ℕ→Poly C)
    (licensed:∀i,K i≠0 → (B.forced i).eligible p.threshold U)(x y:Site n)(D:ℕ)
    (seen:y∈shortTerritory B p K x D):
    y=x ∨ ∃m∈range (Fintype.card (Site n)),∃L∈pathBook (neighbors (2*width p D)) x (m+1),
      L.Nodup ∧ L.toFinset⊆flags p.threshold U ∧ y∈neighbors (width p D) (endSite x L):=by
  let w:=width p D
  let F:=flags p.threshold U
  have claim {z:Site n}(chain:Relation.ReflTransGen (Edge B (shortActors B p K D)) x z):Tether F w x z:=by
    induction chain with
    | refl=>exact Or.inl rfl
    | @tail u z prior step ih=>
      obtain ⟨i,h,ui,zi⟩:=step
      have c:coverNumber p.B (B.forced i).support≤D:=by by_contra no;exact h (if_neg no)
      have alive:K i≠0:=by simpa only [shortActors,if_pos c] using h
      obtain ⟨f,fi⟩:=(B.forced i).inventory_ne
      have flag:f∈F:=(mem_inter.mp ((licensed i alive).1.symm ▸ fi :
        f∈(B.forced i).support∩flags p.threshold U)).2
      have fs: f∈(B.forced i).support:=(B.forced i).inventory_sup fi
      have d:=Nat.add_le_add_right (Nat.mul_le_mul_right (4*p.B+2) c) (2*p.B)
      exact advance ih ⟨f,flag,(Corona.extent _ _ ui fs).trans d,(Corona.extent _ _ fs zi).trans d⟩
  rcases claim (mem_filter.mp seen).2 with eq|⟨a,b,near,reach,far⟩
  · exact Or.inl eq.symm
  obtain ⟨path,simple⟩:=reach.exists_isPath
  let L:=path.support.map Subtype.val
  have booked:L∈pathBook (neighbors (2*w)) x (path.length+1):=list_book path x (by omega)
  have distinct:L.Nodup:=List.Nodup.map Subtype.val_injective simple.support_nodup
  have size:=card_le_univ L.toFinset
  rw [List.toFinset_card_of_nodup distinct,path_book_length _ _ _ booked] at size
  refine Or.inr ⟨path.length,mem_range.mpr (by omega),L,booked,distinct,?_,?_⟩
  · intro z member;obtain ⟨u,_,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp member);exact u.2
  rw [show endSite x L=b.1 from last_walk path x];exact (neighbors_mem _ _ _).2 far

omit [Fintype V] in
/-- The true occupied component is summed on the original law, optionally
inside any further sector. The origin itself costs only that sector's actual
probability. No norm or abundance bound on an unnormalized vacuum gas is used. -/
theorem original_short_reach {T I:Type}{o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)(t:T)
    (μ:Measure (Config G n))[IsProbabilityMeasure μ](x:Site n)(D:ℕ)(event:Set (Config G n))
    {ρ:ℝ}(positive:0≤ρ)(rare:∀Z:Support n,μ.real {U|Z⊆flags P.p.threshold U}≤ρ^Z.card)
    (dilute:(ballCost (2*width P.p D):ℝ)*ρ≤1/2):
    let territory:=fun U:Config G n=>shortTerritory P.activities P.p (fun i=>A.K.hard t i U) x D
    (∑y,μ.real (event∩{U|y∈territory U}))≤
      μ.real event+2*(ballCost (width P.p D):ℝ)*((ballCost (2*width P.p D):ℝ)*ρ):=by
  intro territory
  exact expected_reach μ (neighbors (2*width P.p D)) (neighbors (width P.p D)) _ _
    (neighbors_card _) (neighbors_card _) x (Fintype.card (Site n)) event (fun y=>{U|y∈territory U})
    (fun Z=>{U|Z⊆flags P.p.threshold U}) positive rare dilute
    (fun y U seen=>short_territory_witness P.activities P.p U (fun i=>A.K.hard t i U)
      (fun i=>A.K.charged t i U) x y D seen)

end YM.Integration.FVA1Physical.Marked.RemoteRoster
