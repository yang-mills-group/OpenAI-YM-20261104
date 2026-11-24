import YM.Integration.WilsonVacuumPreResetJointBranch

/-! The comparison is on the actual tagged, Haar-integrated seating supplied
by a retained foreground record. All the tags use the same pure link map. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetJointSeating
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


theorem seated (X : Coat T F) (p : Molecule S) (he : p.toLeft = ∅)
    (sun : flags (Pressure.temp X.x) X.V = ∅) :
    Matter.planted X p = Matter.preps X (Matter.roster p) := by
  have right {A B : Type} : (∅ : Finset (A ⊕ B)).toRight = ∅ := by
    ext i; simp [mem_toRight]
  have hf : (Matter.roster p).flags = ∅ := by
    simp [Matter.roster, he, Packets.store, right]
  unfold Matter.planted
  rw [sun, ← hf]

def linksOn (S : StepData c f) (F : Forest S.ratio) (z : Arguments G c f) : Config G f :=
  fun e => if e ∈ F.trunks then 1 else G.lieExp (z.2 e) * replica S.ratio (Boulevard.actual z.1) e

theorem actual (X : Coat T F) {E : Set ℕ} {r : ℕ} {b : H.fragrances}
    (chosen : Fate.showcase E r b) (i : Option (Fin b.1)) (k : S.Choices)
    (sun : flags (Pressure.temp X.x) X.V = ∅) (Y : F.Slice G) (z : Arguments G c f) :
    field univ (((Matter.preps X (Matter.roster (b.2 i).val)).taggedL k).wrapY Y) z = linksOn S F z := by
  have he := WilsonVacuumPreResetJointBranch.no_seeds chosen i
  have eq := seated (X.taggedL k) (b.2 i).val he sun
  change field univ ((Matter.preps (X.taggedL k) (Matter.roster (b.2 i).val)).wrapY Y) z = _
  rw [← eq]
  exact funext (WilsonVacuumPreResetJointBranch.field_on_sheet (X.taggedL k) _ he sun Y z)

theorem based (X : Coat T F) {E : Set ℕ} {r : ℕ} {b : H.fragrances}
    (chosen : Fate.showcase E r b) (i : Option (Fin b.1)) (k : S.Choices)
    (sun : flags (Pressure.temp X.x) X.V = ∅) (Y : F.Slice G) :
    field univ (((Matter.preps X (Matter.roster (b.2 i).val)).taggedL k).wrapY Y) 0 = 1 := by
  have he := WilsonVacuumPreResetJointBranch.no_seeds chosen i
  change field univ ((Matter.preps (X.taggedL k) (Matter.roster (b.2 i).val)).wrapY Y) 0 = _
  rw [← seated (X.taggedL k) _ he sun]
  exact WilsonVacuumPreResetJointBranch.base (X.taggedL k) _ he sun Y

theorem logarithm (X : Coat T F) {E : Set ℕ} {r : ℕ} {b : H.fragrances}
    (chosen : Fate.showcase E r b) (i : Option (Fin b.1)) (k : S.Choices)
    (sun : flags (Pressure.temp X.x) X.V = ∅) (Y : F.Slice G) (z : Arguments G c f) :
    changes univ (((Matter.preps X (Matter.roster (b.2 i).val)).taggedL k).wrapY Y) z =
      fun e => G.plog (G.mat (linksOn S F z e)) := by
  funext e
  change G.plog (G.mat (field univ (((Matter.preps X (Matter.roster (b.2 i).val)).taggedL k).wrapY Y) z e *
    (field univ (((Matter.preps X (Matter.roster (b.2 i).val)).taggedL k).wrapY Y) 0 e)⁻¹)) = _
  rw [actual X chosen i k sun Y z, based X chosen i k sun Y]
  simp

end YM.Integration.WilsonVacuumPreResetJointSeating
