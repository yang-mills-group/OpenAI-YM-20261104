import YM.Integration.WilsonLongContactUnaryComponent
import YM.Integration.WilsonPositionSeparatedProfileMayerResidentMasks

/-! The genuine singleton in each marked finite ticket, with its complete former source. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactUnaryBallot
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Greenbelt Brim Next.Foundations AnalyticBridge.LocalGaussianLaws
open YM.Integration.WilsonLongContactTown WilsonLongContactFrozenGaussian
open scoped Topology Classical BigOperators
variable {G : Gauge} {c f L : Side} {S : StepData c f} {R : Rep G f} {T : Tube G S}
    {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W x μ α : ℝ} {o : Target.Order G W}
    (H : Cash W x μ L Q o α T R)

open Merge Merge.Palette PhysicalNext.Repeat.WilsonLongContactUnaryHousing
open PhysicalNext.Repeat.WilsonLongContactUnaryComponent PhysicalNext.Repeat.WilsonLongContactUnaryAverage
open PhysicalNext.Repeat.WilsonLongContactUnaryBloom PhysicalNext.Repeat.Legato RG01.Survive RGLocalTaylor
variable {I : Type} (M : I → Leaf R) (i : I)

theorem enrolled (χ : Chi) (V : Config G c) (p : Molecule S) (owns : (M i).turn.badge S∈p) :
    Palette.act M H χ V p (Tickets.mono (Palette.sign M S) i)=
      ((town T (M i)).hire p V).lotus T x χ o.K W o.a Q.table Q.halo V p := by
  rw [Palette.monoAct]
  exact (original (M i) V p owns x χ o.K W o.a Q.table Q.halo V p).symm

theorem full (n : ℕ) (reg : (M i).turn=.logKey n) (χ : Chi) (V : Config G c) :
    let p:=solitary S (M i)
    Palette.act M H χ V p (Tickets.mono (Palette.sign M S) i)=
      masked (Pressure.temp x) (Brim.plate H n).support
        (fun U=>branch (T:=T) (Q:=Q) (x:=x) (o:=o) (W:=W) (M i) χ U) V := by
  apply (enrolled H M i χ V _ ?_).trans (physical H n (M i) reg χ V)
  change (M i).turn.badge S∈({0}:Finset (Fin 1)).map (registry S (address (M i)))
  rw [Finset.map_singleton];exact Finset.mem_singleton_self _

theorem admitted (n : ℕ) (reg : (M i).turn=.logKey n) :
    let A:=Palette.team M (Tickets.mono (Palette.sign M S) i)
    A.signs S=solitary S (M i) ∧ authorized H (A.signs S) ∧ Mayer.Start (A.signs S) := by
  classical
  let A:=Palette.team M (Tickets.mono (Palette.sign M S) i)
  have one : A.own={M i} := by simp [A,Palette.team,Tickets.mono]
  have sign : A.signs S=solitary S (M i) := by rw [Team.signs,one,Finset.image_singleton,solitary,Finset.map_singleton];rfl
  have paid:=WilsonLongContactUnaryHousing.live H n (M i) reg
  have legal : authorized H (A.signs S) := by rw [sign];exact ⟨paid.1,paid.2.1⟩
  exact ⟨sign,legal,WilsonPositionSeparatedProfileMayerResidentMasks.minimal A legal⟩

end YM.Integration.WilsonLongContactUnaryBallot
