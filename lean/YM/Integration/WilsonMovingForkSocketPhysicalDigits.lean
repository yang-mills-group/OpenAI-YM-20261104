import YM.Integration.WilsonMovingForkPhysicalResidues
import YM.Integration.WilsonOriginalPublicNodalChildSites

/-! A physical child and its integer representative have the same complete itinerary. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 420000
noncomputable section
namespace YM.Integration.WilsonMovingForkSocketPhysicalDigits
open Filter Lattice Wilson RG WilsonCoeffUV.Bank
open PhysicalNext.Repeat.Legato
open WilsonMovingForkPhysicalResidues
open WilsonPositionProgramTrialFixedDigits (parents)
open WilsonOriginalPublicNodalChildSites (here)
open scoped Classical Topology
variable {G:Gauge}{I:Type}

theorem ancestor (L:Levels G)(K:ℕ)(z:I → Cover)(m:ℕ)(live:m≤K):
    here L K z m=parents L.S live z:=by
  by_cases fine:m<K
  · rw [here,dif_pos fine,ancestor L K z (m+1) fine]
    funext i
    let A:=L.S.block m
    let B:=(L.S.toDepth fine 0).count
    let C:=(L.S.toDepth live 0).count
    have size:C.val=B.val*A.val:=Next.Rank.Station.size_comp (L.S.oneStep m 0) (L.S.toDepth fine 0) _
    exact (WilsonPositionProgramTrialNestedCenters.combine A B C size (L.S.block_odd m) (z i)).symm
  · obtain rfl:m=K:=by omega
    rw [here,dif_neg (Nat.lt_irrefl _)]
    let u:=L.S.toDepth live 0
    have one:u.count.val=1:=Nat.eq_of_mul_eq_mul_left (L.S.side m 0).property
      (u.exact_size.symm.trans (Nat.mul_one _).symm)
    have same:u.count=1:=Subtype.ext one
    funext i
    change z i=parentC u.count (z i)
    rw [same,WilsonPositionProgramTrialNestedCenters.one]
termination_by K-m
decreasing_by omega

theorem filed (R:Run G){m K:ℕ}(fine:m<K)(per:ℕ){n:ℕ}(z:Fin n → Cover):
    WilsonReceivedChronologicalMaterialSites.digits R (fun i=>wrap (R.family.side K per) (z i)) m=
      WilsonOriginalPublicNodalChildSites.digits R.family.path.levels K z m:=by
  rw [WilsonMovingForkPhysicalResidues.window R (Nat.zero_le m) fine per z]
  funext i
  unfold WilsonPositionProgramTrialFixedDigits.cells WilsonOriginalPublicNodalChildSites.digits
  simp only [dif_pos (show 0 ≤ m ∧ m < K from ⟨Nat.zero_le m,fine⟩)]
  rw [ancestor _ K z (m+1) fine]
  rfl

theorem footprint (R:Run G){m K:ℕ}(live:m+1≤K){n:ℕ}(z:Fin n → Cover):
    ∀ᶠ per:ℕ in atTop,
      WilsonReceivedChronologicalMaterialSites.footprint R (fun i=>wrap (R.family.side K per) (z i)) live=
        here R.family.path.levels K z (m+1):=by
  rw [ancestor _ K z (m+1) live]
  exact WilsonMovingForkPhysicalResidues.registered R live z

end YM.Integration.WilsonMovingForkSocketPhysicalDigits
end
