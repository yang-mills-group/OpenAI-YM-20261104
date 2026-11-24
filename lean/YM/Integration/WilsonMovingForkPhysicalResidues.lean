import YM.Integration.WilsonMovingForkPhysicalCover
import YM.Integration.WilsonReceivedChronologicalMaterialSites

/-! Every active digit in the actually registered torus history is the one
read by the independent cover. All names use the same physical period. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonMovingForkPhysicalResidues
open Filter Lattice RG Wilson Org PhysicalNext PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank
open WilsonPositionProgramTrialCellDigits (packed)
open WilsonPositionProgramTrialFixedDigits (parents cells)
open WilsonReceivedChronologicalMaterialSites (digits physical footprint)
open WilsonMovingForkPrintedFile (parent)
open scoped Classical Topology
variable {G:Gauge}{n:ℕ}

private theorem child {a b:Side}(A:Ratio a b)(z:Cover):
    A.residue (wrap b z)=wrap A.count z:=by
  have eq:A.assemble (wrap a (parentC A.count z),wrap A.count z)=wrap b z:=by
    rw [Ratio.assemble,A.embed_wrap,←map_add,packed]
  exact (congrArg A.residue eq.symm).trans (A.assemble_res _)

theorem window (R:Run G){v j K:ℕ}(vj:v≤j)(jk:j<K)(per:ℕ)(o:Fin n → Cover):
    digits R (fun i=>wrap (R.family.side K per) (o i)) j=cells R.family.path.levels v K o j:=by
  funext a
  have atDate:=congrFun (WilsonMovingForkPhysicalCover.ancestor R jk per o) a
  change physical R (fun i=>wrap (R.family.side K per) (o i)) jk a=
    wrap _ (parents R.family.S jk o a) at atDate
  have enabled:v≤j ∧ j<K:=⟨vj,jk⟩
  have active:j+1≤K:=jk
  simp only [digits,dif_pos active,cells,dif_pos enabled]
  rw [atDate]
  exact child _ _

theorem registered (R:Run G){m K:ℕ}(live:m+1≤K)(o:Fin n → Cover):
    ∀ᶠ per:ℕ in atTop,
      footprint R (fun i=>wrap (R.family.side K per) (o i)) live=parents R.family.S live o:=by
  filter_upwards [WilsonMovingForkPhysicalCover.unwrapped R.family.S (m+1)
    (parents R.family.S live o)] with per fitted
  funext a
  have atDate:=congrFun (WilsonMovingForkPhysicalCover.ancestor R live per o) a
  exact (congrArg lift atDate).trans (fitted a)

end YM.Integration.WilsonMovingForkPhysicalResidues
