import YM.Integration.WilsonSeparatedPrefixCellParents

/-! All selected literal cover sites have their true centered coarse ancestor on the one appointed housing, uniformly in the physical period. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixScreenedParents
open Function Finset Set MeasureTheory Lattice RG Wilson Source OPE RG16 RG16.Literal MergeProof
open PhysicalNext PhysicalNext.Repeat.Legato Table Spec Trace.Pilot Trace.Physical Extra.Histories Motion Extraction Push.GridApprox
open WilsonAddressedPhysicalCells
open scoped Classical BigOperators ENNReal NNReal Topology
variable {G:Gauge}(R:Run G){n:ℕ}
local notation "C" => R.family

theorem original {I:Type}{f p j:ℕ}(height:j+2≤f)(o:I → Cover)(L:ℝ)
    (reach:∀i,‖(C).S.gridPoint f (o i)‖≤L)(room:8*L≤(C).S.a (j+1)):
    ∀i,WilsonOriginalNullOriginGridRoster.ancestry R p f (snap C f p o i) (j+1)=0:=by
  intro i
  have near:=reach i
  have capped:‖(C).S.gridPoint f (o i)‖≤1:=by
    have one:(C).S.a (j+1)≤1:=((C).S.strictAnti.antitone (Nat.zero_le _)).trans_eq (C).S.a_zero
    linarith only [near,room,one]
  have house:(C).S.place (snap (C) f p o i)=(C).S.gridPoint f (o i):=RG16.Literal.inside (C) f p capped
  have zero:=Frontier6.Road.loops_zero (C) p f (j+1) (snap (C) f p o i) (by omega) (by
    rw [house];linarith only [near,room,norm_nonneg ((C).S.gridPoint f (o i))])
  rw [MergeProof.Ribbons.loops,dif_neg (by omega : ¬ f ≤ j+1)] at zero
  simpa only [WilsonOriginalNullOriginGridRoster.ancestry,dif_pos (show j+1≤f by omega)] using zero

end YM.Integration.WilsonSeparatedPrefixScreenedParents
end
