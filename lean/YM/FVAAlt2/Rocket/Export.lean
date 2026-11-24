import YM.FVAAlt2.Rocket.Weekly
import YM.FVAAlt2.Rocket.Poses
import YM.FVAAlt2.Block.Starts
/-!
# Direct formal comparator, step 2 through SOFT pointwise costs for the ledger
 This is the native-fuel theorem on the INFINITE COVER ledger
 from the supplemental existing `RegulatorIR` sources.

 Binding to the full independent LocalFormal conditional CENTERS for the remainder campaign (torus steps),
 proof that the Ledger cover side here on those patches/kernels is the correct interpretation/
 limit, are still additional obligations. Stencils here in exact family units for the perturbative
 problem; does NOT claim a transformation estimate on bare symbols after fitting a separate
 frame.E.Alpha details needed for qlocal. Present combined theorem on this retained Run, schedules
 & prices at ANY Θ generated from thick windows satisfied by optional supplement (real simultaneous
 availability).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Lodge
open Function Set Filter MeasureTheory Topology Real
open Lattice RG Precision Gauge
open Oracle Epoch Calibration Calibration.Notebook Rocket Uniform Binding Diagram Ledger Ledger.Sky Taping Atlas
open YM.FVAAlt2
open PhysicalNext.Repeat.Legato -- FVAAlt2 names overlap
open MS MS.Dial MS.Tide MS.Orbit MS.Port MS.Vista MS.Fleet MS.Land MS.Rake MS.Local.Physical
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {X I:Type} {G:Gauge}{K:KernelChoices}
variable (Y:Oracle.Program K)(Z:∀ Q:Patch,Q.Branches K G)(C:Run G)
variable (SP: Contract C Y Z) (stamp:X→ℕ)(H:∀ x,SP.floor Y Z C ≤ stamp x)
local notation "T₁"=> SP.profile Y Z C stamp H
set_option quotPrecheck false
variable (F: Tent (SP.profile Y Z C stamp H).entire) {g:G.ColorIndex} (μ:ℝ)(p:ℕ)
local notation "B"=> (T₁).desk
local notation "Θ₀"=> (B).dialect Y G Z (sheet F)
open Integration.RunFormalChain
-- this is same Registry with uses to SOME geometry on different periods.In particular any T.L, G actual.
def basisR (C:Run G) : Lobby.Registry C.family.labels C.family.params := ⟨ C.family.localSection,C.makes.sections,YM.FVAAlt2.Block.clothes C⟩
local notation "R"=> basisR C
variable [LinearOrder I][Fintype I]
variable {A: Local.Physical.Deck G}{S: Booked A} {T: MS_Data G S} {T' : Prescription A}
variable {Q: ChartRatio G}(D:I→ Rake.Label A) {l:Filter X}
variable (hver: Calibration.Notebook (SP.profile Y Z C stamp H).desk Y G Z g (native (SP.profile Y Z C stamp H).entire) F p)(hG:G.Simple)
    (hξ: Tendsto stamp l atTop)(hp:∀ x,p≤ stamp x) (hT: TaylorOKPl T (Lobby.Table (basisR C) A) T')
local notation "he'"=> SP.profile Y Z C stamp H
variable (U:X→ Cover)(W:I→ X→ Cover) (hU:(SP.profile Y Z C stamp H).VenueT U)
-- arbitrary geometric test. path animation one p announced; TV.Never reset + cc
local notation "xM"=> (T₁).PoseT μ U W
abbrev physicalCover (S:Prescription A) (k:ℕ):X→ℂ := interpreted B Y Z F ((T₁).stop) R xM μ D S k
include hver hG hξ hp hT hU
theorem narrated (hz:MS.Tide.Profile (xM).profile W)(hm:Rake.Mesh (xM).profile (info W))(k:ℕ)(he:k ≤ p): PeakT.twin l (xM).profile mildG (physicalCover Y Z C SP stamp H F μ D U W T' k) (fun x=> tour T D μ (testP xM x) Finset.univ k):=by
 obtain ⟨hb,hh,h'⟩:=hU.2.2
 let hL:=SP.batch_r Y Z C stamp H hξ
 exact Rocket.final_stage B Y Z F (T₁).stop R xM μ D T'
     (SP.marks Y Z C stamp H p hp) hver (T₁).peak_point (T₁).opens
     (D:= C.metals.O) ( C.alloy.B.ratio ) -- binder `D:=` not Q
     ((T₁).credits Y Z) ⟨ 8,fun w=>by rw [(T₁).shut]; exact le_rfl ⟩ hG (le_max_left ..) hh
     (show (Θ₀).cushion hb (fun x=> Motion.slide 1 (U x)) from h') l ((T₁).era hL) (funext fun i=> ((T₁).payments i).symm) ⟨ U,(T₁).idNear U⟩ ( (T₁).native_costs μ U W hz ) T hT ((T₁).launch μ U W l hU hL hz hm) he
theorem visual(k:I→Tone.QP)(hk:Injective k)(e:ℕ)(he:e≤p): Tendsto (physicalCover Y Z C SP stamp H F μ D U ((T₁).video k) T' e) l (𝓝 (tour T D μ k Finset.univ e)):=by
    have hW:=(T₁).useful U μ k l hU hk (SP.batch_r Y Z C stamp H hξ); let S:=(T₁).picture U μ k
    exact Dial.agrees S (narrated Y Z C SP stamp H F μ p D hver hG hξ hp hT U _ hU hW.total hW.knit e he) hW.upright ((Dial.contin T D k hk Finset.univ e μ).1.tendsto.comp ( Track.comeback (T₁) U μ k l (SP.batch_r Y Z C stamp H hξ) hk ))
end YM.RegulatorIR.FVAAlt2.Lodge
