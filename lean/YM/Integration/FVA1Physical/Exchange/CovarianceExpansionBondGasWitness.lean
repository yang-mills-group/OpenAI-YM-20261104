import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionNativeGasVariation

/-! A changing scalar gas on one locally healthy fine bond requires a
legally contributing roster with one long owner containing both endpoints
and an actual failed inventory site outside the nominated physical collar. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Function MeasureTheory Finset Lattice RG Wilson Push.GridApprox.Attach
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}
local notation "Fld" => Config G n

def longFiled (A:Activities G n)(p:BudgetPoint)(e:Edge (Site n))(r:ℕ)(U:Fld):Prop:=
  ∃s:Finset ℕ, A.gasOccurrence p s U ≠ 0 ∧ ∃j∈s, e.1∈(A.forced j).support ∧
    e.1+step e.2∈(A.forced j).support ∧ r ≤ coverNumber p.B (A.forced j).support ∧
    ∃z∈(A.forced j).inventory,z∈flags p.threshold U ∧ z∉halo (r*leg p.B) {e.1}

/-- Remote failures alone are insufficient. A surviving actor must participate
in a genuinely nonzero *complete legal roster* of the actual scalar gas. -/
theorem gas_change_needs_roster (A:Activities G n)(p:BudgetPoint)(law:A.ForcedFamily p)
    (e:Edge (Site n))(r:ℕ)(U V:Fld)(off:ActualGas.sameOffBond e U V)
    (healthy:Healthy p.threshold (halo (r*leg p.B) {e.1}) U)(after:e.1∉flags p.threshold V)
    (change:A.gas p U ≠ A.gas p V):longFiled A p e r U ∨ longFiled A p e r V:=by
  have before:e.1∉flags p.threshold U:=disjoint_left.mp healthy (halo_subset _ _ (mem_singleton_self _))
  have same:=ActualGas.flags_at_bond e U V off before after
  have ex:∃s:Finset ℕ,A.gasOccurrence p s U ≠ A.gasOccurrence p s V:=by
    by_contra! nn
    exact change (tsum_congr nn)
  obtain ⟨s,diff⟩:=ex
  have ok:A.admissible p U s=A.admissible p V s:=by simp only [Activities.admissible,same]
  have ex':∃j∈s,A.K j U ≠ A.K j V:=by
    by_contra! nn
    apply diff
    unfold Activities.gasOccurrence;rw [ok]
    split
    · exact prod_congr rfl nn
    rfl
  obtain ⟨j,hj,moves⟩:=ex'
  obtain ⟨src,dst⟩:=ActualGas.variable_owner_endpoints A e U V law off same j moves
  have length:=ActualGas.changed_forced_cover A e U V law off same r healthy j moves
  obtain ⟨z,hz⟩:=(A.forced j).inventory_ne
  have odd(W:Fld)(h:A.gasOccurrence p s W ≠ 0):z∈flags p.threshold W:=by
    by_cases live:A.admissible p W s
    · have active:A.K j W ≠ 0:=by
        intro zero;apply h
        simp only [Activities.gasOccurrence,if_pos live]
        exact Finset.prod_eq_zero hj zero
      exact (mem_inter.mp ((law.permit j W active).1.symm ▸ hz)).2
    exact False.elim (h (by simp [Activities.gasOccurrence,live]))
  by_cases hu:A.gasOccurrence p s U=0
  · right
    have hv:A.gasOccurrence p s V ≠ 0:=by simpa only [hu,ne_eq,eq_comm] using diff
    have alarm:=odd V hv
    exact ⟨s,hv,j,hj,src,dst,length,z,hz,alarm,fun near=>disjoint_left.mp healthy near (same.symm ▸ alarm)⟩
  left
  have alarm:=odd U hu
  exact ⟨s,hu,j,hj,src,dst,length,z,hz,alarm,fun near=>disjoint_left.mp healthy near alarm⟩

end YM.Integration.FVA1Physical.Exchange.ShieldedAction
