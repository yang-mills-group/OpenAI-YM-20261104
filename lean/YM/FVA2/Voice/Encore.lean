import YM.FVA2.Voice.Sector
import YM.FVA2.Register.Pressroom
import YM.FVA2.Inked.Combined
/-!
# Both the literal MS endpoints and the compensated-column application

Pure and shifted reads from the same Folio. Headroom for using a stronger geometry
budget is treated elsewhere (`Notch/`). Here use literally the `Dial.Uses` setup.
It gives, among other things, the exact `PhysicalSum` with matching on **all**
sets of mark arguments. `coherent` and `scalePhysics` are the supplied formulations;
we obtain these and the corresponding `coherentF` and `scalePhysicsF`
for the extension. The raw mark coefficients agree with the `LitBook`
analysis (see `Herald`). The extended analysis compares the compensated
marks with the same tuning `team` as in `Main.Match`. Equality of the
intermediate regulator-dependent operator mark costs would be a further result.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Voice
open Function Filter Set Finset MeasureTheory Lattice Wilson
open Maxwell Maxwell.Free
open MS MS.Book MS.Book.Convolve MS.Book.Program MS.Plane MS.Koszul MS.Native MS.Wind MS.Rake MS.Theater MS.Menus MS.Tide MS.Fleet MS.Momentum
open MS.Orbit MS.Swirl MS.Swirl.Near MS.High MS.Vista MS.Land
open Arrival Arrival.Episodic Change Slice Press XPos
open PertExtension FormalOPE.RG10 FormalOPE.RG10.MultiGauge Splice
open scoped Classical Topology BigOperators ContDiff
open MS.Dial MS.Rake MS.Vista
open Register Register.WilsonPrescription
variable {W I:Type}[LinearOrder W] {G:Gauge}(N:Register.WilsonPrescription G)
variable (h:G.Simple)(U:Land.MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (M:Land.Prescription ( Press.portDeck G ))
variable (p:Dial.Trial I W) (v: W→ Label ( Press.portDeck G ))(l:Filter I)(a:ℝ)
set_option quotPrecheck false
local notation "R"=> (N.scheme)
local notation "P"=> ( Position.OpenAxis.Plot ( Press.portDeck G ) )
local notation "Ω"=> (N.analyticChart)
local notation "D"=> MS.Land.MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))
local notation "p0"=> p.profile
local notation "ψ"=> Continuum.Continuation.proofStart h ( Reg.supplies R U )
namespace Ticket
-- Raw application. `birth` highlights the reclosure even from the same multiscale
-- prescription (for Trial side, epoch arbitrary).
structure Herald (dial : Bool) (Z : Fleet.Terrify W I) : Prop
        extends Continuum.Twin R v U p a l (ψ dial) Z where
    birth i (E:Hearth.Epoch G (MS.Orbit.dimT p.side i)) t :
        Core.through R v (p.head i) (fun x=>p.off x i) E Ω (ψ dial) (a-p.profile.θ i) t =
          bury i t Z
lemma raw (dial : Bool) (H : Dial.Uses p l a) :
        ∃! Z : Fleet.Terrify W I, Herald N h U p v l a dial Z := by
    obtain ⟨Z,hZ,hV⟩ := (Continuum.Continuation.plan (Reg.supplies R U) h dial).poses W I p l a v H
    exact ⟨ Z,⟨ hZ, fun i E t=> (Core.deserving ..).trans (hZ.born i t).symm ⟩,
      fun y hy=> hV y hy.toTwin ⟩
-- Apply the extended analysis: satisfy both formulations there (including via `Tide.calledF`)
-- still with the same MS `PhysicalSum`, and now using the W-compensated input. We DO NOT
-- equate all mark costs with the ones on e.g. `ψ true` from the raw-sector matching --
-- only use the same tuning team, see `Main.lean`.
structure Completed (Z : Fleet.Terrify W I) : Prop
        extends toCoherentF : coherentF P U (Press.wickInput R) v p a true M l Z where
    birth i (E:Hearth.Epoch G ( MS.Orbit.dimT p.side i )) t :
        Episodic.start R E Ω v M (p.head i) (fun x=> p.off x i) (a-p.profile.θ i) t = bury i t Z
    removes : ∃ d,
        Tide.scalePhysicsF p.profile P U a M (Press.wickInput R) v p.off p.head p.side true l Z d
    peak i t :
        Top.value R v M (p.head i) (fun x=>p.off x i) (MS.Orbit.dimT p.side i) (a-p.profile.θ i) t =
          bury i t Z

variable (H : Served N U M)
include h H
lemma total (hx : Dial.Uses p l a) : ∃! Z:Fleet.Terrify W I, Completed N U M p v l a Z := by
    obtain ⟨Z,⟨hZ,hv⟩,h'⟩ := H.toPosted.toQuoted.toContract.toMission.cost.purposes a W I v l p hx
    refine ⟨Z,⟨ hZ, fun i E t=>( Episodic.startup .. ).trans (hv i t).symm,
      ?_, fun i t=>(hv i t).symm⟩, fun y hy=> h' y ⟨hy.toCoherentF, fun i t=>(hy.peak i t).symm⟩ ⟩
    obtain ⟨Z',U',hP⟩ := Tide.calledF v p.off hx.total hx.reality hx.upright hx.super h hx.clear
      hx.wind hx.knit ( H.toPosted.toQuoted.toContract.toMission.cost.plan ) true
    refine ⟨ U', ?_ ⟩
    rw [ MS.Dial.separateF _ _ _ hZ.cost ( show CutoffF ( Press.wickInput R ) v p a true M Z'
      from ( fun i s=>hx.reality i ▸ hP.native i s ) ) hZ.init hP.empty ]
    exact hP
/-- Portal at all `Dial.Trial`s satisfying the supplied `Uses` geometry etc. Both results
are for `PhysicalSum` in the **supplied** definition. Though theorems here are on the `MS.Dial`
setup (apply, e.g., at a fixed translation even in the inversion geometry), our actual position
diagnostic comparisons will use the same center averaging prescription across horizons
(`XSpace.Cirrus`); see also `Notch/` for some stronger estimates allowing general centers. -/
theorem posting (dial : Bool) (S' : Dial.Uses p l a) :
    (∃! Z : Fleet.Terrify W I, Herald N h U p v l a dial Z) ∧
      (∃! Z : Fleet.Terrify W I, Completed N U M p v l a Z) :=
    ⟨ raw N h U _ _ _ _ dial S', total N h U M _ _ _ _ H S' ⟩
end Ticket
end YM.FVA2.Voice
