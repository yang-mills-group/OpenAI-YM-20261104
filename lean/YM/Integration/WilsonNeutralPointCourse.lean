import YM.Integration.WilsonNeutralPointCourt
import YM.Integration.WilsonNeutralNativeFreeStep

/-! One finite filed neutral trajectory along the chosen physical child itinerary. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralPointCourse
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open scoped Topology BigOperators Matrix Classical

variable {G:Gauge}(R:Run G){d D:ℕ}(wood:Primer.Families R.family)(a:hue G)(depth:d<D)
variable (digit:∀ i,Site (R.family.S.block i))

abbrev branches (i:ℕ):=(R.family.path.levels.blocks i 0).branches
abbrev quiet (N i:ℕ):Pot G:=Dove.model R.family.path.levels wood (branches R) R.metals.O a N i

def forward (N i:ℕ)(Y:Plaza (R.family.labels.level d) D):Plaza (R.family.labels.level d) D:=
  WilsonNeutralPointMatrix.child (destination R.family.path.levels N i) (wood i)
    (quiet R wood a N (i+1)) a R.metals.O (branches R i) (Elm.growL _ i) d d (digit i) ∘ Y

def reset (N i:ℕ)(Y:Plaza (R.family.labels.level d) D):Plaza (R.family.labels.level d) D:=
  let V:=forward R wood a digit N i Y
  larch V (pantry (R.family.labels.level d) V)⁻¹

def walk (N:ℕ):(h i:ℕ)→Plaza (R.family.labels.level d) D
  | 0,_ => sectionY (R.family.localSection d) depth
  | h+1,i => reset R wood a digit N i (walk N h (i+1))

def filed (N i:ℕ):Plaza (R.family.labels.level d) D:=walk R wood a depth digit N (N-i) i
def transfer (N i:ℕ):Tilework (R.family.labels.level d):=
  pantry _ (forward R wood a digit N i (filed R wood a depth digit N (i+1)))

theorem top (N:ℕ):filed R wood a depth digit N N=sectionY (R.family.localSection d) depth:=by
  simp [filed,walk]

private theorem advance (N i:ℕ)(hi:i<N):filed R wood a depth digit N i =
    reset R wood a digit N i (filed R wood a depth digit N (i+1)):=by
  unfold filed
  conv_lhs=>rw [show N-i=(N-(i+1))+1 by omega]
  rfl

theorem original (N i:ℕ)(simple:G.Simple)(o:Loc G 1)(hi:i≤N)
    (front:d≤R.family.path.levels.clock.J (i+1)):
    Court o (R.family.labels.level d) (filed R wood a depth digit N i):=by
  induction hi using Nat.decreasingInduction with
  | self =>
    rw [top]
    exact Roof.topC o _ _ R.family.params (R.makes.sections d) (Next.Foundations.valuation G d) depth
  | of_succ i bound ih =>
    have upper:=ih (front.trans (R.family.path.levels.fits.mono (Nat.le_succ _)))
    have story:=(Dove.genu R.family.path.levels wood (branches R) R.metals.O a R.alloy.B.ratio simple
      (i:=i+1) (N:=N) bound).toStory
    have money:=WilsonNeutralPointMatrix.filed o (R.family.labels.level d) _ R.metals.O a
      (destination R.family.path.levels N i) (wood i) (branches R i) (Elm.growL _ i)
      _ R.family.params depth front (R.family.path.levels.clock.adm i) story R.alloy.B.ratio upper (digit i)
    rw [advance R wood a depth digit N i bound]
    apply (Roof.tribunal _ _ o _ money).1
    intro b
    exact WilsonNeutralPointCourt.original o (destination R.family.path.levels N i) (wood i)
      (quiet R wood a N (i+1)) (filed R wood a depth digit N (i+1) b) R.metals.O (branches R i) (Elm.growL _ i)
      (digit i) a (upper.officers b) story R.alloy.B.ratio (R.family.path.levels.clock.adm i) d d (slotsFits _ b)

/-- The signed forward field and complete inverse matrix have the same posted source at both endpoints. -/
theorem received (N i:ℕ)(simple:G.Simple)(o:Loc G 1)(hi:i<N)
    (front:d≤R.family.path.levels.clock.J (i+1)):
    let S:=transfer R wood a depth digit N i
    Colfax (slots (R.family.labels.level d)) (Pose.weight (R.family.labels.level d)) S
      (fun v=>Grail.heightK (R.family.S.block i) d (Pose.weight (R.family.labels.level d) v)) ∧
    larch (filed R wood a depth digit N i) S =
      forward R wood a digit N i (filed R wood a depth digit N (i+1)):=by
  intro S
  have upper:=original R wood a depth digit N (i+1) simple o hi
    (front.trans (R.family.path.levels.fits.mono (Nat.le_succ _)))
  have story:=(Dove.genu R.family.path.levels wood (branches R) R.metals.O a R.alloy.B.ratio simple
    (i:=i+1) (N:=N) hi).toStory
  have money:=WilsonNeutralPointMatrix.filed o (R.family.labels.level d) _ R.metals.O a
    (destination R.family.path.levels N i) (wood i) (branches R i) (Elm.growL _ i)
    _ R.family.params depth front (R.family.path.levels.clock.adm i) story R.alloy.B.ratio upper (digit i)
  refine ⟨money,?_⟩
  rw [advance R wood a depth digit N i hi]
  apply (Roof.tribunal _ _ o _ money).2
  intro b
  exact WilsonNeutralPointCourt.original o (destination R.family.path.levels N i) (wood i)
    (quiet R wood a N (i+1)) (filed R wood a depth digit N (i+1) b) R.metals.O (branches R i) (Elm.growL _ i)
    (digit i) a (upper.officers b) story R.alloy.B.ratio (R.family.path.levels.clock.adm i) d d (slotsFits _ b)

end YM.Integration.WilsonNeutralPointCourse
end
