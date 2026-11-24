import YM.Integration.WilsonVacuumPreResetJointRaw
import YM.Integration.WilsonVacuumPreResetPrunedCofactor

/-! On a kept foreground molecule the original Cash criterion excludes seeds.
The Haar input of the true seating is still integrated. On a sunny comparison
sheet the explicit link map inside that integral has all free links active. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetJointBranch
open Function Filter Finset Lattice RG Wilson Tree Pressure Pressure.Stores Pressure.Tube
open ConnectedActivityE6 Shell Coat SliceRows Control Window Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Shoot Precision SectorMeasure Oriented Reserves
open PhysicalNext PhysicalNext.Repeat Height Beam Brim
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open WilsonVacuumPreResetJointField WilsonVacuumPreResetJointRaw RG01Estimate
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W : ℝ} {o : Target.Order G W}
variable {R : Rep G f} {s μ α : ℝ} {H : Cash W s μ L Q o α T R}

/-- The exclusion is a property of the actual previous diagram, including
every one of the molecules selected by its common roster. -/
theorem no_seeds {E : Set ℕ} {r : ℕ} {z : H.fragrances} (chosen : Fate.showcase E r z) :
    ∀ i, (z.2 i).val.toLeft = ∅ := by
  intro i
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact chosen.driver i (Sum.inl a) (Finset.mem_toLeft.mp ha)

theorem doors (X : Coat T F) (p : Molecule S) (he : p.toLeft = ∅)
    (sun : flags (Pressure.temp X.x) X.V = ∅) (Y : F.Slice G) (e : Bond f) :
    ((Matter.planted X p).wrapY Y).Hot e ↔ e ∉ F.trunks := by
  have empty : ((Matter.planted X p).wrapY Y).seeds.place = ∅ := by
    have left {A B : Type} : (∅ : Finset (A ⊕ B)).toLeft = ∅ := by
      ext i; simp [mem_toLeft]
    have right {A B : Type} : (∅ : Finset (A ⊕ B)).toRight = ∅ := by
      ext i; simp [mem_toRight]
    simp [left, right, Coat.wrapY, Matter.planted, Matter.preps, Matter.roster, Packets.store, Stores.place, he, sun]
  simp [Coat.Hot, Shell.active, Shell.frozen, Stores.dome, empty, Lattice.halo]

theorem field_on_sheet (X : Coat T F) (p : Molecule S) (he : p.toLeft = ∅)
    (sun : flags (Pressure.temp X.x) X.V = ∅) (Y : F.Slice G) (z : Arguments G c f) (e : Bond f) :
    field Finset.univ ((Matter.planted X p).wrapY Y) z e =
      if e ∈ F.trunks then 1 else G.lieExp (z.2 e) * replica S.ratio (Boulevard.actual z.1) e := by
  rw [at_bond]
  have all : walls Finset.univ X.V z.1 = Boulevard.actual z.1 := by ext1 q; simp [walls]
  by_cases h : e ∈ F.trunks
  · have notHot := (doors X p he sun Y e).not.mpr (not_not_intro h)
    rw [if_neg notHot, if_pos h]
    exact F.on_tree _ ⟨e, h⟩
  · rw [if_pos ((doors X p he sun Y e).mpr h), if_neg h]
    exact congrArg (fun V => G.lieExp (z.2 e) * replica S.ratio V e) all

theorem base (X : Coat T F) (p : Molecule S) (he : p.toLeft = ∅)
    (sun : flags (Pressure.temp X.x) X.V = ∅) (Y : F.Slice G) :
    field Finset.univ ((Matter.planted X p).wrapY Y) 0 = 1 := by
  ext1 e
  rw [field_on_sheet X p he sun Y]
  simp [Precision.replica, Boulevard.actual, Work.F03.represent_link]

end YM.Integration.WilsonVacuumPreResetJointBranch
