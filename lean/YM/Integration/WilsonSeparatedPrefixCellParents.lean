import YM.Integration.WilsonSeparatedPrefixCellProfile
import YM.Integration.WilsonOriginalTwoFlatGrid
import YM.Integration.WilsonOriginalNullOriginGridRoster
import YM.Integration.WilsonThermometerUnchangedGrouping

/-! A nonzero correlated cell keeps its true Wilson ancestors. On a bounded
housing all of them are the single centered site, independently of the period. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCellParents
open Function Finset Set MeasureTheory Lattice RG Wilson Source OPE RG16 RG16.Literal MergeProof
open PhysicalNext PhysicalNext.Repeat.Legato Table Spec Trace.Pilot Trace.Physical Extra.Histories Motion Extraction Push.GridApprox
open WilsonAddressedPhysicalCells
open scoped Classical BigOperators ENNReal NNReal Topology
variable {G:Gauge}(R:Run G){n:ℕ}
local notation "C" => R.family

theorem original (φ:Test n){f p j:ℕ}(h:j+2≤f)(r L:ℝ)
    (bound:∀x:Points n,φ x≠0→∀i,‖r • x i‖≤L)
    (room:8*(L+4*(n:ℝ)*(C).S.a f)≤(C).S.a (j+1))
    (o:Sites ((C).side f p) n)(active:mass φ ((C).S.a f) r ((C).side f p) o≠0):
    ∀i,WilsonOriginalNullOriginGridRoster.ancestry R p f (o i) (j+1)=0:=by
  obtain ⟨x,placed,supp⟩:=WilsonSeparatedPrefixCellProfile.active φ _ r _ ((C).S.a_pos f) o active
  let site:=Extraction.address ((C).S.a f) (r • x)
  intro i
  have dist:=Extraction.approximate ((C).S.a_pos f) (r • x)
  rw [dist_eq_norm] at dist
  have close:‖(C).S.gridPoint f (site i)-r • x i‖≤4*(n:ℝ)*(C).S.a f:=(PiLp.norm_apply_le (tag ((C).S.a f) site - r • x) i).trans dist
  have near:‖(C).S.gridPoint f (site i)‖≤L+4*(n:ℝ)*(C).S.a f:=by
    have q:=norm_sub_le_norm_sub_add_norm_sub ((C).S.gridPoint f (site i)) (r • x i) 0
    simp only [sub_zero] at q
    calc
      _≤‖(C).S.gridPoint f (site i)-r • x i‖+‖r • x i‖:=q
      _≤_:=by linarith only [show ‖(C).S.gridPoint f (site i)-r • x i‖≤4*(n:ℝ)*(C).S.a f by exact close,bound x supp i]
  have capped:‖(C).S.gridPoint f (site i)‖≤1:=by
    have one:(C).S.a (j+1)≤1:=((C).S.strictAnti.antitone (Nat.zero_le _)).trans_eq (C).S.a_zero
    linarith only [near,room,one]
  have house:(C).S.place (o i)=(C).S.gridPoint f (site i):=by
    rw [←placed];exact RG16.Literal.inside (C) f p capped
  have zero:=Frontier6.Road.loops_zero (C) p f (j+1) (o i) (by omega) (by
    rw [house];linarith only [near,room,norm_nonneg ((C).S.gridPoint f (site i))])
  rw [MergeProof.Ribbons.loops,dif_neg (by omega : ¬ f ≤ j+1)] at zero
  simpa only [WilsonOriginalNullOriginGridRoster.ancestry,dif_pos (show j+1≤f by omega)] using zero

theorem housing {c:Side} (B:ℕ)(route:Fin n→Site c)(pinned:∀i,route i=0):
    ∀i k,coverNumber B ({route i,route k}:Support c)≤1:=by
  intro i k
  simpa [pinned] using (WilsonThermometerUnchangedGrouping.alone B (0:Site c))

end YM.Integration.WilsonSeparatedPrefixCellParents
end
