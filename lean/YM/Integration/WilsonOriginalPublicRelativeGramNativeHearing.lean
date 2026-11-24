import YM.Integration.WilsonOriginalPublicRelativeGramNativePooledRank
import YM.Integration.WilsonOriginalPublicRelativeGramNativeUniform
import YM.Integration.WilsonOriginalPublicRelativeGramNativeSalary

/-! A signed self reading on the original UV and period tails. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramNativeHearing
open Filter Set Function Lattice Wilson RG Source OPE Extraction RG17 Table Spec Climb
open XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick MS MS.Menus MS.Land MS.Theater Local.Physical
open FVA2 FVA2.Register PhysicalNext.Repeat.Legato Trace.Pilot PhysMS XSpace.Cirrus Pert.Asymptotics
open WilsonOriginalPublicRelativeGramPosted (Dated submitted deposits gram)
open WilsonOriginalPublicRelativeGramFreePanel (named)
open WilsonOriginalPublicRelativeGramOriented (maxwell)
open WilsonOriginalPublicRelativeGramReflectedLimit (ordered)
open WilsonOriginalPublicRelativeGramNativePivot (Ruler filed)
open WilsonOriginalPublicRelativeGramNativeMeasure (beam)
open WilsonOriginalPublicRelativeGramNativeCeiling (Adequate)
open WilsonPositionProgramTrialOpticalBand (Bracket)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator

open WilsonOriginalPublicRelativeGramNativePooledRank (Accepts)
open WilsonOriginalPublicRelativeGramNativeUniform (above)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator

variable {G:Gauge}(B:Deck G)(h:ℕ)(a:Axis)(R:Run G)(f:Extraction.Order)
local notation "I" => Glyph B h
local notation "Z" => ℝ×(ℕ×ℕ)
local notation "d" => (fun _:I=>h)
local notation "physical" => ordered trail (fun _:ℝ=>f.fuse)

theorem original {C:ℝ}(booked:Accepts B h a C)(pres:WilsonPrescription G)
    {simple:G.Simple}{M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {test:Prescription (Press.portDeck G)}{dial:Bool}(verified:Main.Match pres simple M test dial)
    (avoid:Finset E4)(L:Ruler R pres.run){A:ℝ}(ap:0≤A)(cut:Bracket R L.cut A)
    (Y:ℝ→(ℕ×ℕ)→I→R.family.label h)(paper:ℝ→Dated (L:=Unit) R pres.scheme d)(q:ℕ)
    (w:ℝ→ℝ)(u e t:Z→I→ℝ):
    let sale:=fun z:Z=>filed R pres B h a avoid L q z.1 (paper z.1)
    let amp:=fun z:Z=>(sale z).frame false z.2
    (∀ᶠr in trail,1≤w r) →
    (∀j:I,∀ᶠz:Z in physical,‖beam B h a R pres.run avoid L Y z j j‖≤(w z.1)^2) →
    (∀j:I,∀ᶠz:Z in physical,
      ‖beam B h a R pres.run avoid L Y z j j-submitted R pres.scheme d (sale z) false z.2 j j‖≤1) →
    (∀j:I,∀ᶠz:Z in physical,0≤u z j ∧ e z j*u z j≤1 ∧ e z j*(u z j)^2≤1 ∧ t z j≤1 ∧
      deposits R pres.scheme d (sale z) false z.2 j j≤
        e z j*(2*u z j*‖fun i:I=>amp z i j‖+(u z j)^2)+t z j) →
    ∀ᶠz:Z in physical,‖amp z‖≤C*w z.1:=by
  intro sale amp restored gross heard older
  let H:=fun z:Z=>gram R pres.scheme d (sale z) z.2
  have stable:=WilsonOriginalPublicRelativeGramNativeUniform.original R pres B h a avoid L paper q verified ap cut
  apply booked amp H (fun z=>w z.1) u e t
    (stable.mono_left (WilsonOriginalPublicRelativeGramNativeUniform.cofinal R L f))
  have days:=WilsonOriginalPublicRelativeGramNativePivot.first trail (fun _:ℝ=>f.fuse)
  filter_upwards [days.eventually restored,eventually_all.mpr gross,eventually_all.mpr heard,
    eventually_all.mpr older] with z cash hit hear paid
  refine ⟨cash,fun j=>⟨(paid j).1,(paid j).2.1,(paid j).2.2.1,(paid j).2.2.2.1,?_⟩⟩
  let onField:=beam B h a R pres.run avoid L Y z j j
  let named:=submitted R pres.scheme d (sale z) false z.2 j j
  let signed:=((amp z)ᴴ * H z * amp z) j j
  have old:‖signed-named‖≤deposits R pres.scheme d (sale z) false z.2 j j:=by
    rw [norm_sub_rev]
    exact WilsonOriginalPublicRelativeGramPosted.printed R pres.scheme d (sale z) false z.2 j j
  have originalHit:‖named-onField‖≤1:=by rw [norm_sub_rev];exact hear j
  have toField:=norm_sub_le_norm_sub_add_norm_sub signed named onField
  have total:=norm_add_le (signed-onField) onField
  rw [sub_add_cancel] at total
  change ‖signed‖≤_
  linarith only [total,toField,old,originalHit,(paid j).2.2.2.2,show ‖onField‖≤(w z.1)^2 from hit j]

end YM.Integration.WilsonOriginalPublicRelativeGramNativeHearing
