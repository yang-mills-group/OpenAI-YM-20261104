import YM.Integration.WilsonThermometerWeakMovedCovers

/-! Two actual translated weak observations lie in different original reflection cells
even when their two microscopic residues and their interior radii differ. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakJointCells
open Function Filter Set Lattice RG Push Next.Extract Dash Cells Next.Rank
open WilsonThermometerWeakMovedCovers WilsonThermometerWeakMixedCells
open scoped Classical Topology
variable (S:Schedule)

theorem original : ∃e:ℕ,∀(k m N p:ℕ)(hk:k≤N)(r:Fin 2→ℕ)(deep:∀i,m+e+1≤r i)(live:∀i,r i≤N)
    (z:Fin 2→Site (S.side N p)) (b:Fin 2 → Cover),
    (∃j:Axis,S.a m+S.a k≤|S.gridPoint k (b 0) j-S.gridPoint k (b 1) j|) →
    (∀j:Axis,2*(|S.gridPoint k (b 0) j-S.gridPoint k (b 1) j|+S.a k+S.a m)<(S.side m p).val*S.a m) →
    let h:m≤N:=by have h:=deep 0;have w:=live 0;omega
    let T:=center S p h 0
    let w:=fun i=>move S p hk (z i) (wrap _ (b i))
    ∃(t:Site (S.side N p)) (c₀ c₁:Site (S.side m p)),c₀≠c₁ ∧
      w 0+t∈T.margin c₀ (3*span S (live 0) p) ∧
      w 1+t-move S p hk (z 1) 0∈T.margin c₁ (3*span S (live 1) p):=by
  obtain ⟨e,due⟩:=WilsonThermometerWeakMovedExperiment.original S
  refine ⟨e,?_⟩
  intro k m N p hk r deep live z b separation period h T w
  obtain ⟨u₀,h₀,near⟩:=letter S p hk (z 0) (b 0)
  obtain ⟨u₁,h₁,at₁⟩:=displacement S p hk (z 1) (b 1)
  let u:Fin 2 → Cover:=![u₀,u₁]
  have costs (a:Axis): |S.gridPoint k (b 0) a-S.gridPoint k (b 1) a|≤
      |S.gridPoint N (u 0) a-S.gridPoint N (u 1) a|+S.a k ∧
      |S.gridPoint N (u 0) a-S.gridPoint N (u 1) a|≤
      |S.gridPoint k (b 0) a-S.gridPoint k (b 1) a|+S.a k:=by
    change _≤|S.gridPoint N u₀ a-S.gridPoint N u₁ a|+_ ∧ |S.gridPoint N u₀ a-S.gridPoint N u₁ a|≤_
    rw [at₁]
    have p₀:=abs_sub_le (S.gridPoint k (b 0) a) (S.gridPoint N u₀ a) (S.gridPoint k (b 1) a)
    have p₁:=abs_sub_le (S.gridPoint N u₀ a) (S.gridPoint k (b 0) a) (S.gridPoint k (b 1) a)
    have close:=near a
    rw [abs_sub_comm (S.gridPoint k (b 0) a) (S.gridPoint N u₀ a)] at p₀
    constructor <;> linarith
  obtain ⟨j,gap⟩:=separation
  have gee:∃a:Axis,S.a m≤|S.gridPoint N (u 0) a-S.gridPoint N (u 1) a|:=⟨j,by linarith [(costs j).1]⟩
  obtain ⟨t,c,diff,rooms⟩:=due m N p r deep live u gee (fun a=>by linarith [(period a),(costs a).2])
  refine ⟨t,c 0,c 1,diff,?_,?_⟩
  · simpa only [w] using (show move S p hk (z 0) (wrap _ (b 0))+t∈T.margin (c 0) _ by rw [← h₀];exact rooms 0)
  have right:w 1-move S p hk (z 1) 0+t∈T.margin (c 1) (3*span S (live 1) p):=by change move S p hk (z 1) _ -move S p hk (z 1) 0+t∈_;rw [←h₁];exact rooms 1
  rw [show w 1+t-move S p hk (z 1) 0=w 1-move S p hk (z 1) 0+t by abel];exact right

end YM.Integration.WilsonThermometerWeakJointCells
end
