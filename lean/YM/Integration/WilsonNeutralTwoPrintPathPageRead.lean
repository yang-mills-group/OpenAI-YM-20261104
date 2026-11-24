import YM.Integration.WilsonNeutralTwoPrintPathPageReturn
import YM.Integration.WilsonOriginalSelfPeriod
import YM.Integration.WilsonNeutralTwoPrintPathJet

/-! Folding an absolutely summable covered angular tensor through nested
periods preserves every component on a periodically repeated held link. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonNeutralTwoPrintPathPageRead
open Function Lattice RG WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer
open Further.PhysicalPeriodLimitF933 Macrame Shingle
open scoped Classical BigOperators

variable {V α:Type}[NormedAddCommGroup V][CompleteSpace V][Fintype α]
variable {n X:Side}{r:ℕ}

def lower (h:n.val∣X.val)(z:(Site X × α)):(Site n × α):=(splitter h z.1,z.2)

omit [Fintype α] in
theorem twice (h:n.val∣X.val)(z:Fin r→Cloth α):lower h ∘ slideC X z=slideC n z:=by
  funext i
  exact Prod.ext (Macrame.branch h (z i).1) rfl

theorem coefficient (h:n.val∣X.val)(K:Ten V (Cloth α) r)
    (paid:Summable (fun z=>‖K z‖))(y:Fin r→(Site n × α)):
    (∑x:Fin r→(Site X × α),if lower h ∘ x=y then plume K X x else 0)=plume K n y:=by
  let row(x:Fin r→(Site X × α))(z:Fin r→Cloth α):V:=
    if lower h ∘ x=y then peglet K X x z else 0
  have sums(x:Fin r→(Site X × α)):Summable (row x):=by
    apply Summable.of_norm
    apply paid.of_nonneg_of_le (fun _=>norm_nonneg _)
    intro z
    by_cases eqn:lower h ∘ x=y <;> by_cases hit:slideC X z=x <;> simp [row,peglet,eqn,hit]
  calc
    _ = ∑x:Fin r→(Site X × α),∑'z,row x z:=by
      apply Finset.sum_congr rfl
      intro x _
      by_cases eqn:lower h ∘ x=y <;> simp [row,eqn,plume]
    _ = ∑'z,∑x:Fin r→(Site X × α),row x z:=(Summable.tsum_finsetSum (fun x _=>sums x)).symm
    _ = plume K n y:=by
      apply tsum_congr
      intro z
      calc
        _ = ∑x:Fin r→(Site X × α),if x=slideC X z then
              (if lower h ∘ slideC X z=y then K z else 0) else 0:=by
          apply Finset.sum_congr rfl
          intro x _
          by_cases eqn:x=slideC X z
          · subst x
            simp [row,peglet]
          · simp [row,peglet,eqn,Ne.symm eqn]
        _ = peglet K n y z:=by simp [peglet,twice]

variable [NormedSpace ℝ V]

theorem held (h:n.val∣X.val)(K:Ten V (Cloth α) r)
    (paid:Summable (fun z=>‖K z‖))(test:V →L[ℝ] ℂ)(weights:(Fin r→Site n × α)→ℂ):
    (∑x:Fin r→Site X × α,test (plume K X x)*weights (lower h ∘ x))=
      ∑y:Fin r→Site n × α,test (plume K n y)*weights y:=by
  calc
    _ = ∑x:Fin r→Site X × α,∑y:Fin r→Site n × α,
        if lower h ∘ x=y then test (plume K X x)*weights y else 0:=by simp
    _ = ∑y:Fin r→Site n × α,∑x:Fin r→Site X × α,
        if lower h ∘ x=y then test (plume K X x)*weights y else 0:=Finset.sum_comm
    _ = _:=by
      apply Finset.sum_congr rfl
      intro y _
      rw [←coefficient h K paid y,map_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hit:lower h ∘ x=y <;> simp [hit]

end YM.Integration.WilsonNeutralTwoPrintPathPageRead
end

