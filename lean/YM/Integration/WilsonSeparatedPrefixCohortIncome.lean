import YM.Integration.WilsonSeparatedPrefixCohortUnscale
import YM.Integration.WilsonSeparatedPrefixCanonicalSoft

/-! The whole masked ordinary peer on the issued canonical program is integrable at its actual finite dates, with its own scalar retained. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCohortIncome
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Extra.Histories.Relay Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many RG05Readout.Pantry Records
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Motion Bandage
open Extra.Multi Extra.Trajectories ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus
open Trace.Physical.GermGraph Lodestar WilsonThermometerUnitFilingCoarse WilsonOriginalCompanionLinearFiling
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedSource
open scoped Classical BigOperators Topology
open WilsonOriginalMicroscopicEntranceDeposits (funded)
open WilsonSeparatedPrefixCohortUnscale (product)
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][DecidableEq I]{N p f:ℕ}{d:I→ℕ}
local notation "P" => R.family.path.rep N p f
local notation "Jo" => Marks I
local notation "X" => Config G (R.family.side f p)

private theorem pupil (o:I→Site (R.family.side f p))(i:I)(φ:X→ℂ)(c:Poly Jo)(M:Support (R.family.side f p)→X→Poly Jo)
    {σ α fee:ℝ}{B:ℕ}{w:I→ℝ}(burn:∀Z,Burns o Z (M Z) σ)(towed:Towed w id M B α fee)
    (row:∀U,Poly.send ((Jo).fire i) (φ U)=c+∑Z,M Z U):funded φ:=by
  let s: (Jo).Mode:=(Jo).fire i
  have scalar(U):φ U=c.part s+∑Z,(M Z U).part s:=by
    have h:=congrArg (fun v:Poly Jo=>v.part ((Jo).fire i)) (row U)
    rw [Poly.part_send,if_pos rfl] at h
    change φ U=c.part s+(∑Z,M Z U).part s at h
    simpa only [Poly.part_sum] using h
  obtain ⟨_,_,_,tokens⟩:=towed
  choose bound _ bills _ using tokens
  refine ⟨?_,‖c.part s‖+∑Z,bound Z s,?_⟩
  · rw [show φ=(fun U=>c.part s+∑Z,(M Z U).part s) from funext scalar]
    exact measurable_const.add (Finset.measurable_sum _ fun Z _=>(burn Z).me s)
  · intro U
    rw [scalar]
    apply (norm_add_le ..).trans
    exact add_le_add_right ((norm_sum_le _ _).trans (Finset.sum_le_sum fun Z _=>bills Z U s)) _

theorem original (live:f≤N)(ref:∀i,R.family.ref (d i)≤f)(o:I→Site (R.family.side f p))
    (q:∀i,Coefficient (R.family.labels.level (d i)) (R.family.side f p))
    (format:∀i,(q i).Format (o i) R.family.params (P))
    {κ:ℝ}{B:I→ℝ}(cap:∀i,(q i).remBound (o i) (P) κ (B i))(wide:1≤(P).p.supportExponent)(s:Finset I):
    Integrable (fun U=>((P).eval U:ℂ)*product s (fun i=>(q i).exponentialEntry (o i) (R.family.localSection (d i)) (P)) U) (prior G _):=by
  have paid(i:I):funded ((q i).exponentialEntry (o i) (R.family.localSection (d i)) (P)):=by
    obtain ⟨c,M,_,_,burn,towed,row⟩:=WilsonSeparatedPrefixCanonicalSoft.original (J:=Jo) R live (ref i) o i (q i) (format i)
      (fun _=>1) (fun _=>zero_lt_one) (cap i) wide
    exact pupil R o i _ c M burn towed row
  obtain ⟨me,b,bb⟩:=WilsonSeparatedPrefixCohortUnscale.salary s _ paid
  have val:=actualTransport_weighted_integrable R.family R.makes live me.aestronglyMeasurable bb (le_refl f)
  simpa only [actualTransport_base R.family R.makes live,Complex.real_smul] using val

end YM.Integration.WilsonSeparatedPrefixCohortIncome
end
