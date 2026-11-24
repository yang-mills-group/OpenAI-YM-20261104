import YM.Integration.WilsonAddressedEquationAllowance

/-! The common paid equation section on the measured grade-six, four, four
station. Every estimate applies to its original face coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedThermometerIntake
open Function Filter Set Finset Metric MeasureTheory Lattice Wilson RG Source Labels Extraction Table Spec
open OPE OPE.Orbits Climb Trace.Pilot Next.UVStress RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading Next.Extract MergeProof Extension
open Extra.Histories Extra.Histories.Motion Bid Push Bandage
open WilsonAddressedEquationShelf WilsonAddressedEquationMoments
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G)
set_option quotPrecheck false
local notation "C!"=> R.family
local notation "a!"=> R.alloy.B.a

/-- Price on the actual raw coefficients once the physical reference and weak date have been fixed.
The explicit factor also records the cost before either cutoff when their raw norm is bounded. -/
theorem original (simple:G.Simple) :
    ∃ (V:∀ d,SectionData ((C!).labels.level d)) (W:Mark.Weave G), ∃ P b,
      (∀ d,Mark.Portfolio (C!).params (V d) (W d)) ∧ Hearthside (C!) V W P b (fly (a!)) ∧
      Placed R V P b ∧
      ∃ (E:ℕ→ℕ→ℝ) (U:∀ d:ℕ, ℕ→ℕ→((C!).labels.level d).Index→(C!).label d),
      (∀ d,Hearth (C:=C!) (V d) (fly (a!)) (E d) (fun N p=>P d (N,p)) (U d) ∧
        ∀ᶠ N:ℕ in atTop, ∀ p j, Issued (C!) (V d) N p R.w (far (a!)) (waybill (a!)) (fly (a!))
          R.doors j (E d N) (U d N p j)) ∧
      ∀ (f:Extraction.Order) (Y:Ultrafilter UVIndex), (Y:Filter _) ≤ f.fuse →
      ∀ A:Group (C!) 6, Tendsto A.station.wheel.atCut (Y:Filter _) (𝓝 A.lift) →
      ∀ᶠ z:UVIndex in (Y:Filter _), ∀ (s:Badge) (i:Fin 3) (w:ℕ),
        let H := (C!).labels.level (grade i).val
        let x:(C!).label (grade i).val := A.station.wheel.atCut z (index A (grade i)) (vector A s i)
        orbitCost H*H.coeffSize ((P (grade i).val z).symm
          (((C!).factory (grade i).val z.1 z.2).terminal.symm (x-b.step (grade i).val z x))) *
          abs (E (grade i).val z.1) / gainChart (C!).path z.1 w ≤
          (2*Fintype.card H.Index*orbitCost H)*Real.exp ((C!).S.scale w/8-3*(C!).S.scale z.1/32) := by
  obtain ⟨V,W,P,b,portfolio,house,course⟩ := WilsonAddressedEquationCourse.original R simple
  choose E U school issued using course
  refine ⟨V,W,P,b,portfolio,house,placed R V W P b portfolio house,E,U,fun d=>⟨school d,issued d⟩,?_⟩
  intro f Y filt A moves
  have mesh : Tendsto Prod.fst (Y:Filter UVIndex) atTop :=
    tendsto_atTop.mpr fun j=>(large_mesh f j).filter_mono filt
  apply eventually_all.mpr
  intro s
  apply eventually_all.mpr
  intro i
  let j := index A (grade i)
  let v := vector A s i
  let B := ‖A.lift j v‖+1
  have camera : Continuous (fun l : Lifts (C!) A.horizon=>l j) := continuous_apply j
  have atField : Continuous (fun a:(Bel (C!).book).Field j→L[ℂ](C!).book.Ref j=>a v) :=
    (ContinuousLinearMap.apply ℂ ((C!).book.Ref j) v).continuous
  have limit := (atField.comp camera).continuousAt.tendsto.comp moves
  have bounded : ∀ᶠ z:UVIndex in (Y:Filter _), ‖A.station.wheel.atCut z j v‖ ≤ B :=
    (limit.norm.eventually (eventually_lt_nhds (lt_add_one _))).mono fun _ h=>h.le
  filter_upwards [bounded,mesh.eventually (WilsonAddressedEquationAllowance.paid R.makes house (school (grade i).val) B)]
    with z ball price w
  exact price z.2 (A.station.wheel.atCut z j v) ball w

end YM.Integration.WilsonAddressedThermometerIntake
