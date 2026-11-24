import YM.Integration.WilsonNeutralNativeFreeStep
import YM.Integration.WilsonNeutralParityInverse
/-! The independently enrolled full normalized field retains coupling/rank
parity at every nonbare date, with its actual quiet program and inverse. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralSourceParity
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonRunFormalMarkedStep WilsonNeutralNormalizedForestStep
open scoped Topology BigOperators Matrix Classical

variable {G : Gauge} (R : Run G) {d D : ℕ} (wood : Primer.Families R.family)
variable (a : hue G) (depth : d < D) {U : ℕ → ℕ}
variable (grant : WilsonWindowFormalPurchase.Canonical U R.kit)

open WilsonNeutralParityWick WilsonNeutralParityInverse
def Sector {I:Type*}(s:I→ℕ)(Y:I→Anthem D G):Prop:=∀ u f,Parity (s u) (Y u f)

theorem projected {F:Frame G d}{Y:Letter F→Anthem D G}(hy:Sector (Pose.slots F) Y):
    WilsonNeutralParityInverse.Signed (Pose.slots F) (Roof.pantry F Y):=by
  intro i j e wrong
  exact WilsonNeutralParityReset.entry (hy j) i e (by omega)

theorem divided {I:Type*}[Fintype I][DecidableEq I]{s:I→ℕ}{Y:I→Anthem D G}
    (hy:Sector s Y){M:Matrix I I Pence}(ok:WilsonNeutralParityInverse.Signed s M):
    Sector s (Roof.larch Y M):=by
  intro b f e r live
  by_contra wrong;apply live
  simp only [Roof.larch,Finset.sum_apply]
  apply Finset.sum_eq_zero;intro u _
  unfold Kemp.launch Kemp.surf;apply Finset.sum_eq_zero;intro pair hpair
  have bound:=Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
  by_cases empty: Y u f pair.2 r=0
  · rw [empty,smul_zero]
  · have h:=hy u f pair.2 r empty
    rw [ok u b pair.1 (by omega),zero_smul]

private abbrev br (i:ℕ): (R.family.path.levels.clock.op i 0).patch.Branches
    R.family.path.levels.clock.kernel G:= (R.family.path.levels.blocks i 0).branches

private def raw (N i:ℕ):Roof.Plaza (R.family.labels.level d) D:=
    Roof.migrates a (destination R.family.path.levels N i) (wood i)
      R.family.path.levels.clock.kernel
      (Dove.model R.family.path.levels wood (br R) R.metals.O a N (i+1)) R.metals.O (br R i)
      (Elm.growL R.family.path.levels i) d d ∘ graph R wood a depth N (i+1)

private theorem propagated (N i:ℕ)(simple:G.Simple)(hi:i<N)
    (hy:Sector (Pose.slots (R.family.labels.level d)) (graph R wood a depth N (i+1))):
    Sector (Pose.slots (R.family.labels.level d)) (raw R wood a depth N i):=by
  intro b f
  let P:=destination R.family.path.levels N i
  let W:=Dove.model R.family.path.levels wood (br R) R.metals.O a N (i+1)
  have story:Story W (Next.Free.pink R.family.path.levels.clock.kernel.penalty P.wing):=
    (Dove.genu R.family.path.levels wood (br R) R.metals.O a R.alloy.B.ratio simple
      (i:=i+1) (N:=N) hi).toStory
  exact WilsonNeutralParityReset.block a P (wood i) W R.metals.O (br R i) (Elm.growL _ i)
    story R.alloy.B.ratio (R.family.path.levels.clock.adm i) d d (graph R wood a depth N (i+1) b)
    (hy b) f

include grant in
theorem field (N i:ℕ)(simple:G.Simple)(o:Loc G 1)(hi:i≤N)
    (front:d≤R.family.path.levels.clock.J (i+1)):
    Sector (Pose.slots (R.family.labels.level d)) (graph R wood a depth N i):=by
  induction hi using Nat.decreasingInduction with
  | self =>
    rw [WilsonRunFormalMarkedStep.graph,Elm.terrace_zero]
    exact WilsonNeutralParityReset.bare (R.family.localSection d) depth
  | of_succ i hi ih =>
    have h:=propagated R wood a depth N i simple hi
      (ih (front.trans (R.family.path.levels.fits.mono (Nat.le_succ _))))
    have orig:=WilsonNeutralNativeFreeStep.original R wood a depth grant N i simple o hi front
    rw [←WilsonNeutralAppointedForestStep.step R wood a depth grant] at orig
    have ok:WilsonNeutralParityInverse.Signed (Pose.slots (R.family.labels.level d)) (matrix R wood a depth N i):=projected h
    rw [WilsonRunFormalMarkedStep.graph,Elm.thickets _ _ _ _ _ _ _ _ _ _ hi]
    exact divided h (WilsonNeutralParityInverse.inverse _ _ orig.det ok)

include grant in
theorem original (N i:ℕ)(simple:G.Simple)(o:Loc G 1)(hi:i<N)
    (front:d≤R.family.path.levels.clock.J (i+1)):
    WilsonNeutralParityInverse.Signed (Pose.slots (R.family.labels.level d)) (Primer.fieldStep R.family a wood depth N i):=by
  rw [←WilsonNeutralAppointedForestStep.step R wood a depth grant]
  exact projected (propagated R wood a depth N i simple hi (field R wood a depth grant N (i+1) simple o hi
    (front.trans (R.family.path.levels.fits.mono (Nat.le_succ _)))))

include grant in
theorem first (N i:ℕ)(simple:G.Simple)(o:Loc G 1)(hi:i<N)
    (front:d≤R.family.path.levels.clock.J (i+1))
    (x y:Letter (R.family.labels.level d))(same:Pose.slots _ x%2=Pose.slots _ y%2):
    coeff 1 (Primer.fieldStep R.family a wood depth N i x y)=0:=
  original R wood a depth grant N i simple o hi front x y 1 (by omega)

end YM.Integration.WilsonNeutralSourceParity
end
