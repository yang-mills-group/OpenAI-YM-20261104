import YM.Integration.WilsonPositionProgramPublicPositionNormalization
import YM.Integration.WilsonPositionProgramPublicBasisOperator

/-! The four actual reflected bills on each of the determining columns give
one operator-norm bound on the shared, finite physical normalization. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicFourOperator
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open GapsContact GapsContact.Stamps GapsContact.Seams GapsContact.Ascent
open Trace Trace.Terrace Trace.Pilot MergeProof.East PhysicalNext.Repeat.Legato
open RG17 FullVolume Climb Next.UVStress PhysMS Maxwell XSpace XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Scale MS MS.Fleet MS.Land FVA2.Register MS.Menus Local.Physical Table.Pairing
open WilsonMatrixTicketLanesSmearedPivot WilsonPositionProgramPublicMicroscopic
open WilsonPositionHomogeneousFrame WilsonThermometerUnitFilingFourSquare WilsonMeasuredPublicBank
open WilsonPositionProgramPublicStations WilsonPositionProgramPublicGram WilsonPositionProgramPublicMeasuredAxes
open WilsonPositionProgramPublicReflectedRead WilsonPositionProgramPublicWickGram
open WilsonPositionProgramPublicContrast WilsonPositionProgramPublicWide WilsonPositionProgramPublicTunedHearing
open WilsonPositionProgramPublicPositionNormalization WilsonPositionProgramPublicFittedInverse
open scoped Topology BigOperators Classical
variable {G:Gauge}{R:Run G}{S:Table R.family.book}{f:Extraction.Order}
    {l:Ultrafilter (ℕ×ℕ)}{d:ℕ}(F:Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G)
    (B:Deck G)(axis:Axis)(A:ℝ→WilsonPositionThermometerCapStation.Group R.family 6)
    (index:ℝ→ℕ)(p:Profiles R d)(b:Bulb (center axis) axis){r:ℝ}(hr:0<r)(q:ℕ)
    {budget:ℕ}(P:Handoff.Directory Z (index r) budget)
    (arms:Bool→(y:S.Field d)→Arm R.family S (l:Filter _) d y)
    (L:(p.probes.index→ℂ)→L[ℂ](Bel R.family.book).Field d)
local notation "Γ" => Glyph B d
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z

def comparison (c:Four ℝ)(moving:Bool){t:ℝ}(ht:0<t)(e:ℝ)(z:ℕ×ℕ)(i:Γ):Prop:=
  let w:=Pi.basisFun ℂ Γ i
  let entry:=fun branch=>coordinate B F J Z p hr arms L branch z w
  let matrix:=WilsonPositionProgramPublicDirectoryBoard.table Z axis b q (id:Γ→Γ) P
    (WilsonPositionBareSimultaneous.parameter Z index θ r (source F J Z A r moving z)) c
  let arm:=fun (j:Γ) br=>arms br (WilsonPositionProgramPublicMeasuredAxes.position B F J Z (r:=r) j)
  ∀br s,‖assay (weighted (id:Γ→Γ) (r/t) (entry br))
      (weighted (id:Γ→Γ) (r/t) (entry s)) matrix-
      WilsonPositionProgramPublicWideHearing.paid F arm axis b ht w z br s‖≤e

def Fits (z:ℕ×ℕ)(U:(Γ→ℂ)≃ₗ[ℂ](Γ→ℂ)):Prop:=
  (∀w,coordinate B F J Z p hr arms L true z (U w)=coordinate B F J Z p hr arms L false z w) ∧
  (∀w,‖U w-w‖≤condition R B d*‖coordinate B F J Z p hr arms L false z w-
    coordinate B F J Z p hr arms L true z w‖) ∧
  ∀w,fee B F J Z p hr arms false z ((axes R B d).equivFun.symm w)=
    fee B F J Z p hr arms true z ((axes R B d).equivFun.symm w)→U w=w

def Control (k:ℝ):Prop:=
  ∃U:(ℕ×ℕ)→((Γ→ℂ)≃ₗ[ℂ](Γ→ℂ)),
    (∀ᶠ z in (l:Filter _),Fits F J Z B p hr arms L z (U z)) ∧
    ∀c∈(Z.run.step (index r)).Box,∀moving:Bool,∀(t:ℝ)(ht:0<t),r≤t→∀e:ℝ,
      (∀ᶠ z in (l:Filter _),∀i:Γ,comparison F J Z B axis A index p b hr q P arms L c moving ht e z i)→
      ∀η:ℝ,0<η→∀ᶠ z in (l:Filter _),
        k*((r/t)^d*‖(U z).toLinearMap.toContinuousLinearMap-ContinuousLinearMap.id ℂ (Γ→ℂ)‖)^2≤
          (Fintype.card Γ:ℝ)^2*condition R B d^2*(4*e+η)

theorem original {k:ℝ}(hk:0≤k)(order:(l:Filter _)≤f.fuse)(reads:∀y,L (samples F J Z p r y)=y)
    (listen:BasisHearing F J Z B axis A index p b k hr q P arms L):
    Control F J Z B axis A index p b hr q P arms L k:=by
  let U z:=if h:∃T,Fits F J Z B p hr arms L z T then h.choose else LinearEquiv.refl ℂ (Γ→ℂ)
  have paid:∀ᶠ z in (l:Filter _),Fits F J Z B p hr arms L z (U z):=by
    filter_upwards [WilsonPositionProgramPublicFittedInverse.original B F J Z p hr arms L reads order] with z h
    have h':∃T,Fits F J Z B p hr arms L z T:=h
    simpa only [U,dif_pos h'] using h'.choose_spec
  refine ⟨U,paid,?_⟩
  intro c member moving t ht wide e four η hη
  let basis:=Pi.basisFun ℂ Γ
  let entry (z:ℕ×ℕ)(br:Bool)(i:Γ):=coordinate B F J Z p hr arms L br z (basis i)
  have own (i:Γ):∀ᶠ z in (l:Filter _),k*((r/t)^d*‖entry z false i-entry z true i‖)^2≤4*e+η :=
    listen c member moving t ht wide (fun _=>basis i) (charge (basis i)) e
      (.of_forall fun _=>le_rfl) (four.mono fun z h=>h i) η hη
  filter_upwards [paid,eventually_all.mpr own] with z fits due
  let Δ:=(U z).toLinearMap.toContinuousLinearMap-ContinuousLinearMap.id ℂ (Γ→ℂ)
  have row (i:Γ):k*((r/t)^d*‖Δ (basis i)‖)^2≤condition R B d^2*(4*e+η):=by
    have scale:0≤(r/t)^d:=pow_nonneg (div_nonneg hr.le ht.le) _
    have cap:(r/t)^d*‖Δ (basis i)‖≤condition R B d*((r/t)^d*‖entry z false i-entry z true i‖):=by
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (fits.2.1 _) scale
    calc
      _ ≤ k*(condition R B d*((r/t)^d*‖entry z false i-entry z true i‖))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg scale (norm_nonneg _)) cap 2) hk
      _ = condition R B d^2*(k*((r/t)^d*‖entry z false i-entry z true i‖)^2):=by ring
      _ ≤ _ :=mul_le_mul_of_nonneg_left (due i) (sq_nonneg _)
  simpa only [mul_assoc] using WilsonPositionProgramPublicBasisOperator.original Δ hk row

end YM.Integration.WilsonPositionProgramPublicFourOperator
