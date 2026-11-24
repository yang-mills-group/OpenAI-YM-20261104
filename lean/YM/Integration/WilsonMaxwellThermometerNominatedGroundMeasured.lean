import YM.Integration.WilsonMaxwellThermometerNominatedGroundMoment

/-! Squarefree identification of the actual normalized Gibbs moment of the
nominated compensated field, on the complete corrected telescope. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedGroundMeasured
open Filter MeasureTheory Lattice Wilson Labels RG Source PhysicalNext.Repeat.Legato RG17
open OPE OPE.Orbits Table Spec PhysMS PhysMS.Frame Maxwell Maxwell.Free XSpace XSpace.Rose XSpace.Normalize
open Marker Climb Trace Trace.Pilot Extraction WilsonPositionCapTransport WilsonPositionThermometerGradedSource
open WilsonPositionThermometerCapStation WilsonCenteredPhysicalPanel WilsonThermometerCenteredAlgebra
open WilsonMaxwellThermometerNominatedGroundMoment WilsonMaxwellThermometerNominatedGroundCell
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G)
local notation "C" => R.family
local notation "W" => WilsonMaxwellThermometerNominatedGroundPurse.policy R
local notation "J₀" => Stock.census (Fin 3)

theorem quiet (A:Group (C) 6) (z:ℕ×ℕ) (o:Sites R z 3):
    (C).omega z.1 z.2 (face R A z o ∅)=1:=by
  have constant:(face R A z o ∅:Config G (R.family.side z.1 z.2)→ℂ)=fun _=>1:=by
    funext U
    simp [face,WilsonCapturedPrimaryWardRestoration.filed]
  rw [constant]
  unfold Family.omega Wilson.moment
  rw [integral_const,probReal_univ,one_smul]

theorem charged (p:Badge→ℂ) (qu:p ∅=1) (Q:Poly J₀):
    (total (WilsonMaxwellThermometerNominatedGroundPurse.table p) Q).part full=
    ∑s:Badge,weight Q (mode s)*p s:=by
  rw [affine,←(modes.sum_comp (fun t=>weight Q t*(WilsonMaxwellThermometerNominatedGroundPurse.table p).part t))]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  change (if mode s=(J₀).quiet then 1 else p s)=p s
  split_ifs with h
  · have eq:=congrArg Subtype.val h
    change s=∅ at eq
    exact eq ▸ qu.symm
  · rfl

theorem original {f:Extraction.Order} {S:Table (C).book} (F:Final C f S) (J:ℝ→tower S) (V:Store G)
    (A:ℝ→Group (C) 6) {Y:Ultrafilter (ℕ×ℕ)} {H:(Bel (C).book).Hierarchy}
    (prior:(Y:Filter _)≤f.fuse) (book:Book (f:=f) (l:=Y) (H:=H) A J) (lead:Leading F J) (φ:Test 3):
    ∀ᶠw:ℝ×(ℕ×ℕ) in trail.curry (Y:Filter _),
      let Z:=WilsonPositionCorrectedCap.adjusted F J V A w.1
      (C).omega w.2.1 w.2.2 (integrated R Z w.1 w.2 φ)=
        φ.applyTo (fun x=>(total (WilsonMaxwellThermometerNominatedGroundPanel.actual R F J V A w x) (W x)).part full):=by
  have enrolled:=WilsonPositionCorrectedCap.original F J V A book lead
  have measured:=WilsonMaxwellThermometerNominatedGroundMoment.original R F J V A prior book lead φ
  apply eventually_curry_iff.mpr
  filter_upwards [enrolled 0,eventually_curry_iff.mp measured] with r qualified current
  let Z:=WilsonPositionCorrectedCap.adjusted F J V A r
  have words:=faces R Z qualified.2.1 (fun j=>(qualified.2.2.2.2.1 j).2.1)
  filter_upwards [words.filter_mono prior,current] with z same seen
  refine seen.trans ?_
  congr 1
  funext x
  let o:=WilsonCenteredCompactBooking.site R r z x
  apply (charged _ _ _).symm
  exact (same o ∅).symm.trans (quiet R Z z o)

end YM.Integration.WilsonMaxwellThermometerNominatedGroundMeasured
