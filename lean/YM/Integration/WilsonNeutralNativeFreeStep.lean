import YM.Integration.WilsonNeutralAppointedForestStep

/-! The leading matrix at every finite top, on the actual independently
filed field program. A single slot multiplicity and own-weight block has
exactly its engineering matrix, including every off-diagonal entry. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralNativeFreeStep
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonRunFormalMarkedStep WilsonNeutralNormalizedForestStep
open scoped Topology BigOperators Matrix Classical

variable {G : Gauge} (R : Run G) {d D : ℕ} (wood : Primer.Families R.family)
variable (a : hue G) (depth : d < D) {U : ℕ → ℕ}
variable (grant : WilsonWindowFormalPurchase.Canonical U R.kit)

private theorem filed (N i:ℕ)(simple : G.Simple)(o : Loc G 1)(hi:i<N)
    (front:d≤R.family.path.levels.clock.J (i+1)) :
    Colfax (Pose.slots (R.family.labels.level d)) (Pose.weight (R.family.labels.level d))
      (matrix R wood a depth N i)
      (fun j=> Grail.heightK (R.family.S.block i) d (Pose.weight (R.family.labels.level d) j)):=by
  have upper:=WilsonRunFormalMarkedStep.normalized R wood a depth simple o N (i+1) hi
    (front.trans (R.family.path.levels.fits.mono (Nat.le_succ _)))
  let br:∀ k,(R.family.path.levels.clock.op k 0).patch.Branches
      R.family.path.levels.clock.kernel G:=fun k=>(R.family.path.levels.blocks k 0).branches
  have quiet:=(Dove.genu R.family.path.levels wood br R.metals.O a R.alloy.B.ratio simple
    (i:=i+1) (N:=N) hi).toStory
  exact Roof.performed o (R.family.labels.level d) _ R.metals.O a
    (destination R.family.path.levels N i) (wood i) (br i) (Elm.growL _ i) _ R.family.params
    depth front (R.family.path.levels.clock.adm i) quiet R.alloy.B.ratio upper

include grant in
theorem original (N i:ℕ)(simple : G.Simple)(o : Loc G 1)(hi:i<N)
    (front:d≤R.family.path.levels.clock.J (i+1)) :
    Colfax (Pose.slots (R.family.labels.level d)) (Pose.weight (R.family.labels.level d))
      (Primer.fieldStep R.family a wood depth N i)
      (fun j=> Grail.heightK (R.family.S.block i) d (Pose.weight (R.family.labels.level d) j)):=by
  rw [←WilsonNeutralAppointedForestStep.step R wood a depth grant]
  exact filed R wood a depth N i simple o hi front

include grant in
theorem own_weight (N i:ℕ)(simple : G.Simple)(o : Loc G 1)(hi:i<N)
    (front:d≤R.family.path.levels.clock.J (i+1))
    (x y:Letter (R.family.labels.level d))
    (slots:Pose.slots _ x=Pose.slots _ y)(left:Pose.weight _ x=d)(right:Pose.weight _ y=d):
    coeff 0 (Primer.fieldStep R.family a wood depth N i x y) =
      if x=y then 1 else 0 :=by
  have H:=original R wood a depth grant N i simple o hi front
  have h:=H.diagonal x y slots (le_of_eq (left.trans right.symm))
  rw [right] at h
  have pos:0<((R.family.S.block i).val:ℝ):=by exact_mod_cast (R.family.S.block i).property
  simpa [Grail.heightK,Dawn.scale,inv_pow,ne_of_gt pos] using h

end YM.Integration.WilsonNeutralNativeFreeStep
end
