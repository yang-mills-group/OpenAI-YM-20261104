import YangMills.WilsonProof.NativeSupport.NativeBoardAdmission
import YangMills.WilsonProof.NativeSupport.JointFundedVisit

/-! A single constant board contains the actual selected incoming
representative and has the actual next representative as its moment.
The numerical one-letter price and the measured integral can therefore
be spent on precisely the same dated visit. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility
open RG Wilson Lattice PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Legato.Campaign PhysicalNext.Repeat.Muse
open PhysicalNext.Repeat.Pass PhysicalNext.Repeat.Jams PhysicalNext.Repeat.Muse.Veil
open Extra.Iteration FullVolume.Ray FullVolume.Urns Progress.DirectedRecipe
open PhysicalNext.Repeat.Roof RG.Shoot
open scoped Classical
variable {G : Gauge} {R : Run G} (T : Campaign R) {N per : ℕ}

theorem physical_joint_visit (i : Fin N) :
    let H := T.L.prim N i per i.isLt
    let X := (halls T per N).plan (i.val+1) i.isLt
    ∃ y : Board (A:=R.alloy) N i per X,
      y.val.val.val=R.T.history N per (i.val+1) ∧
      H.moment y.val.val=R.T.history N per i ∧ Orchard.Visit H y.val.val ∧
      ∃ Y, SectorOn (A:=R.alloy) (fun _ : sun => y.val.val) Y := by
  intro H X
  let p := T.center N per
  obtain ⟨x,fin,fout⟩:=p.twines i i.isLt
  obtain ⟨f,factor,⟨Z,_⟩,center⟩:=physical_scalar_sector T i
  let y₀:=f Jams.tip
  obtain ⟨a,read₀⟩:=y₀.property
  have ea : y₀.val.val.val.activities=x.val.activities := (factor Jams.tip).1.trans (congrArg Rep.activities fin).symm
  have eb : y₀.val.val.val.beta=x.val.beta := by
    have z: y₀.val.val.val.beta=fromLambda (R.alloy.B.a.clock.hatBeta (i.val+1)) (p.pitch i.succ) := by
      simpa only [Jams.tip,add_zero] using (factor Jams.tip).2
    exact (z.trans center).trans (congrArg Rep.beta fin).symm
  have sp : HasSlots x.val.p x.val.activities := by
    rw [x.property.1.point,← ea,← y₀.val.val.property.1.point]
    exact y₀.val.property
  let k : Ticket R.alloy N i per := ⟨x,sp⟩
  let y : Board (A:=R.alloy) N i per X := ⟨k,a,read₀.norm,eb.symm.trans read₀.takes,ea.symm.trans read₀.bills⟩
  have retained : R.alloy.B.bake.retain N (i.val+1) per y.val.val.val := by
    change R.alloy.B.bake.retain N (i.val+1) per x.val
    rw [fin]
    rcases T.L.altitude.mp (p.rises.prices (i.val+1) (Nat.zero_le _) i.isLt).1 with ⟨_,_,_,_,held⟩
    exact held
  refine ⟨y,fin,fout.symm,(BoardAdmission.visit_iff_retained T i.isLt y).mpr retained,?_⟩
  let base : RG.Shoot.band R.alloy.B.a (i.val+1) := ⟨x.val.beta,x.property.2⟩
  let pose : FullVolume.Ray.Fold _ _ :=
    { Z.pose with peak:=1,slope:=0,funds:=by norm_num,covers:=by simpa using Z.pose.full.2.2 }
  let Y : Mist _ _ _ _ := ⟨base,pose,fun _=>base,fun _ _=>by simp [pose,Fold.flow]⟩
  refine ⟨Y,⟨fun _=>rfl,fun _ _=>rfl,?_,?_⟩⟩
  · intro v j
    exact ⟨_,ink.termC _,fun _=>rfl⟩
  · intro v j
    exact ⟨_,ink.termC _,fun _=>rfl⟩

end YM.Integration.InletSusceptibility
