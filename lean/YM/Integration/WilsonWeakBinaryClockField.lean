import YM.RG17.Vaults
import YM.RG17.Rook
import YM.Integration.WilsonWeakBinaryTileAngle

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWeakBinaryClockField
open Function Filter Finset Lattice Wilson RG Tree Next.Rank.Spindle Stationary Exterior
open Comparison.RG02 RG17 PhysicalNext PhysicalNext.Repeat.Legato RemainderComparison ConnectedActivityE6
open scoped Classical Topology
variable {G:Gauge}(R:Run G)

theorem original (simple:G.Simple)
    (columns:∀ᶠ j in atTop,(R.family.path.levels.params j).columns ≤ R.family.path.levels.clock.hatBeta j):
    ∀ᶠ i in atTop, ∀{N p:ℕ}(_hi:i<N)(D:ClockFace R 4 i N p)(α:(R.family.labels.level 4).Index),
      let g:=Coat.gStep (R.family.path.rep N p (i+1)).beta
      let frame:=(R.family.path.rep N p i).p
      let money:=R.family.path.levels.budget i
      let x:=(D.tiles α).val
      let b:=WilsonWeakBinaryTileAngle.link frame g x
      let angle:=Stationary.arm G (R.family.side i p) 1 b
      let U:=net frame 0 (sizeQ R.family i) x
      Integral.sample g angle=U ∧ flags frame.threshold U=∅ ∧
      ∃ z:ℝ, |z| ≤ (money.B:ℝ)^2*money.threshold/g ∧ ∀e,‖Exterior.collect G angle e‖ ≤ |z|:=by
  filter_upwards [paidThrough R.family 4 R.makes simple columns] with i admitted
  intro N p hi D α g frame money x b angle U
  have gp:0 < g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson hi))
  have ht:‖x‖ ≤ 1:=(D.tiles α).property.trans (inv_le_one_of_one_le₀
    (one_le_pow₀ ((R.family.path.levels.fits.delayed i).le) (n:=6)))
  have same:frame=money:=(R.makes.wilson.represents N p i hi.le).vac
  refine ⟨(WilsonWeakBinaryTileAngle.original frame g gp x).1,(admitted N p hi.le).1 x (D.tiles α).property,?_⟩
  obtain ⟨z,hz,hd⟩:=WilsonWeakBinaryTileAngle.admitted frame g gp x ht
  exact ⟨z,by simpa only [same] using hz,hd⟩

end YM.Integration.WilsonWeakBinaryClockField
end
