import YM.Integration.WilsonMarkedInheritedGaussianKernel

/-! One precision-inverse price for every deposited upper action on the actual patch. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramUniformNoise
open Function Filter Finset Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free
open Work.F08 Stationary Tree FormalBulk08 Flat Reef FormalBulk08.Bank FormalBulk08.Jets
open scoped Topology BigOperators Matrix Classical
variable {G:Gauge}{K:KernelChoices}

theorem original (P:Patch)(L:Lodge P)(h:P.Branches K G):
    ∃ σ:ℝ,1≤σ ∧ ∀(V:Train P.J)(n:Side),
      let S:=Flat.primary P K n
      let F:=L.forest (S:=S)
      ∀ x y,|(Flat.testPrecision G S F V)⁻¹ x y|≤σ:=by
  obtain ⟨η,hη,forests⟩:=Flat.center_price G K P.J P.order_cut
  obtain ⟨C,_,allV⟩:=forests P rfl h
  obtain ⟨A,_,hh,_⟩:=L.close_staged G K 1 one_pos
  let t:=min 1 η
  have ht:0<t:=lt_min one_pos hη
  have close: (Lodge.closeRow G P K L).strip t A:=strip_mono hh (min_le_left ..) le_rfl
  let a:ℝ:=Fintype.card (ParcelG G P.L)
  let limit:=a*((a*(A*C))*A)
  refine ⟨max 1 limit,le_max_left ..,?_⟩
  intro V n S F x y
  obtain ⟨U,hr,hU⟩:=allV V
  have narrow:U.strip t C:=strip_mono hU (min_le_right ..) le_rfl
  have folded:(L.power K U).strip t limit:=strip_compose ht.le (strip_compose ht.le close narrow) (strip_trans close)
  have table:=(Lodge.catalogue_power K G L V P.order_cut h ⟨η,C,hη,hU⟩ hr n).2
  have exactTable:=Matrix.inv_eq_right_inv table
  rw [exactTable]
  exact (WilsonMarkedInheritedGaussianKernel.folded (L.power K U) ht.le folded n _ _).trans (le_max_right ..)

end YM.Integration.WilsonPositionProgramUniformNoise
end
