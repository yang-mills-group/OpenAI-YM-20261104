import YM.FVA2.Scale.Beta
import YM.FVA2.Arrival.Episodes
/-!
# One converted comparison with scale law

This formal-to-formal conversion includes the final check-frame N and uses
the engineering powers from the `Scale` modules.

`ν` in this file is in the logarithmic convention of `YM/MS`. For example use
`ν = Teller.logNu 1` (see `Teller/Mass.lean`) to assert results at unit MS mass.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Scale.System
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Level Reg.Point Reg.Token Reg.Unique Reg.Choice Facets Equator Measure Jury
open Meter GroupS
variable {G:Gauge}(Y: Initialize G){V: Normalize.Store G}(K:Rose.Pick V)
variable (T: MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable (S:Prescription (Press.portDeck G)) (h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)(hr:Favors.Horder S)(hu:Ace.UnitP S)
variable (ν:ℝ) {d:ℕ}
local notation "φ"=> Measure.f K ν T
local notation "χ"=> GroupS.ψ K T ν
local notation "ξ"=> GroupS.Ψ K T ν
local notation "Z"=> Measure.Z Y K ν T
local notation "H"=> Measure.start Y K
local notation "U"=> Measure.outlook Y K
abbrev Readout (ν:ℝ)(d:ℕ): Reports G d:= realm ( Measure.Z Y K ν T d ) (substitute ( Measure.f K ν T ) (Reg.State.kernel ν T d))
/-- Independent Wilson reports at finite regulator. -/
abbrev positions (d:ℕ) (a:Mesh) : Reports G d:= realm (adjust Y K d) ( Rose.proposed Y K a d )
lemma arrays : Readout Y K T ν d= realm (adjust Y K d) (Reg.Faith.reports ν K T d):= ( Normalize.parlance _ _ _ ).symm
include h hs hr hu
lemma evaluate : Orders (U d) (Readout Y K T ν d):= ( ( Measure.compares Y K ν T S h hs hr hu ) ▸ ( ( initial ν T ).glance φ |>.specify (Z d) ) )
lemma limit (d:ℕ): Reg.Higher.HasAll Front (fun i=> positions Y K d i) (Readout Y K T ν d):= by
    intro i n t p; rw [arrays Y K T ν]; unfold positions; simp_rw [ really (adjust Y K d) ]; exact tendsto_finsetSum _ (fun j _=> Reg.Faith.tents ν Y K S T h hs hr hu ( j none ) n t (pulseU j (adjust Y K d) p) )
-- gather extensive costs and physical hypotheses.
omit h hs hr hu
open Arrival.Episodic
structure Laws (ν:ℝ)(p m:ℝ→Cn)(A B:ℝ→Frames G) : Prop where
    check : Law (Measure.outlook Y K) p A
    minimal : Law (wave ν T) m B
    intertwines t: (m t).subst ( Measure.f K ν T )=( Measure.f K ν T ).subst ( p t )
    fields t d: stepV ( Measure.f K ν T ) ( B t d ) * stepV (p t) ( Measure.Z Y K ν T d )=Measure.Z Y K ν T d * A t d
    dif : ( Beta.beta m ).subst (Measure.f K ν T)= PowerSeries.derivative ℂ (Measure.f K ν T) * Beta.beta p
structure Contract (S:Prescription (Press.portDeck G)) : Prop extends Mission K T Y S where
    price_v : Precise.Prepare Y K (Measure.adjust Y K) ∧
      ∀ D, Precise.Prepare Y K D→ D=Measure.adjust Y K
    cpl ν: Tangent (Measure.f K ν T)
    meant : Scale.Select.meter K (Measure.start Y K 6)=PowerSeries.X
    joint ν d:
      Base (Measure.Z Y K ν T d) ∧ Native (Measure.Z Y K ν T d) ∧
      PowerCondition d (Measure.start Y K d) (Measure.adjust Y K d)
    series ν d:
      actMark (Measure.Z Y K ν T d) ( couple ( Measure.f K ν T ) (wave ν T d) )=
        Measure.outlook Y K d
    sees {a b} (H':a≤b) ν :
      Walk H' ( Measure.Z Y K ν T a ) ( Measure.Z Y K ν T b ) ∧
      Inherited ( Measure.outlook Y K a ) ( Measure.outlook Y K b ) H'
    smear ν d:
      Orders (Measure.outlook Y K d) (Readout Y K T ν d) ∧
      Reg.Higher.HasAll Front (fun i=> positions Y K d i) (Readout Y K T ν d)
    scales ν : Laws Y K T ν ( GroupS.ψ K T ν ) ( GroupS.Ψ K T ν )
      (GroupS.gaugeN Y K T ν) (GroupS.gaugeM Y K T ν)
    uniques ν (p:Cn)(D: Frames G): Tangent p →(∀ i,Base (D i))→
      (∀ i, actMark ( D i ) ( couple p ( wave ν T i ) )=Measure.outlook Y K i )→
      p=Measure.f K ν T ∧ D=Measure.Z Y K ν T
include h
theorem promotes (H0:Mission K T Y S): Contract Y K T S:= by
    obtain ⟨hs,hr,hu⟩:= H0.toSchemeV.born
    exact ⟨ H0,⟨ ( Precise.only 0 Y K T S h hs hr hu _ ).2 rfl, fun D=> ( Precise.only 0 Y K T S h hs hr hu D ).mp ⟩,fun v=> Specific.vigor_f Y K v T S h hs hr hu, Select.overcome Y K 0 T S h hs hr hu,fun v d=>⟨ litZ Y K v T S h hs hr hu, precise Y K v T S h hs hr hu, Measure.adj Y K v T S ( d:=d ) h hs hr hu ⟩, fun v d=> Measure.compares Y K v T S h hs hr hu, fun {i} {j} H' ν=>⟨ walks_o Y K ν T S h hs hr hu H', paths Y K ν T S h hs hr hu H' ⟩, fun ν d=>⟨ evaluate Y K T S h hs hr hu ν,limit Y K T S h hs hr hu ν d ⟩,fun ν=> ⟨ Precise.mainN ν Y K T S h hs hr hu, Precise.mainM ν Y K T S h hs hr hu, contract0 ν Y K T S h hs hr hu,fun t d=> contractM ν Y K T S h hs hr hu t, Beta.translated ν Y K T S h hs hr hu⟩, fun ν p D=> Specific.unique_map Y K ν T S h hs hr hu p D⟩
/-- Unified formal scheme converter.
 On EXACT $Y : Initialize G$ including physical stencils and K position prescription
 (operators of any horizon through finite arity, before orthogonal alignment). Require the
 continuum $MS_Data$ prescription at one compatible Plot choice. Then `Measure.f` and `Measure.Z` are genuine
 and satisfy scale and running law. $s$ log length exponent. $dial$ selects which of the
 *two MS proof endpoints* to extract the lattice tuning from (`Continuation`).
 `Contract.toMission` includes Step1 Fk etc in scope specified.
 -/
theorem converter (dial:Bool): ∃ S: Prescription (Press.portDeck G), S.team=( Continuum.Continuation.proofStart h (Reg.supplies Y T) dial).team ∧ Contract Y K T S:= by obtain ⟨S,hs,hu⟩:= checkpoint5 Y K T h dial; exact ⟨S,hs,promotes Y K T _ h hu⟩
omit h
/-- Existence without *physical data* hypotheses. -/
theorem checkpoint6 (G:Gauge)(h:G.Simple)(dial:Bool): let Y:= XSpace.Initialize.standard G; ∃ (V:Normalize.Store G) (K:Rose.Pick V) (T: MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (S:Prescription (Press.portDeck G)), S.team=( Continuum.Continuation.proofStart h (Reg.supplies Y T) dial ).team ∧ Contract Y K T S:= by intro Y; obtain ⟨V,K,T,S,hS,H'⟩:= Episodic.come_up G h dial; exact ⟨V,K,T,S,hS,promotes Y K T _ h H'⟩
end YM.FVA2.Scale.System
