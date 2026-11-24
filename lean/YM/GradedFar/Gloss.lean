import YM.Integration.WilsonPositionHomogeneousComparison
import YM.GradedFar.Compass
/-!
# Signature corollary WPHC through ANY through-order q

On our *earlier physical* input, unchanged Frame & MS data. Thus continuation along the actual
original comparison, not merely `formal >= formal`, and provenance/interpretation exactly as in
that original manuscript's qexactcorr predicate.

See also Age with the extended arities/caps & derivatives & phases goal. This one covers
all fixed operands of signature including unnormalized, any requested ε.
No assertion that this previous physical data (C5, F.3 hypothesis etc) has been supplied independently.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
open Wilson RG Source Extraction Table Spec PhysicalNext.Repeat.Legato RG17 FullVolume
open Function Filter Set PowerSeries Climb Trace.Pilot PhysMS OPE OPE.Orbits
open XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale
open MS MS.Native MS.Land MS.Fleet
open Dframe O O.Score O.Enh FVA2.GradedFar Tariff
open WilsonPositionHomogeneousComparison (matchesThrough)
open scoped Topology BigOperators Classical
variable {G : Gauge} {n h :ℕ} {R:PhysicalNext.Repeat.Legato.Run G}
    {f:Extraction.Order} {S:Table R.family.book} (U:Final R.family f S) (J:ℝ→PhysMS.tower S)
    (lead:Leading U J) (N:WilsonPrescription G)
variable {hG:G.Simple} (M: MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ:MS.Land.Prescription (Press.portDeck G)}
    (H:Main.Match N hG M σ true) (ν:ℝ)
local notation "t"=>WilsonPositionHomogeneousFrame.reading U J N
local notation "W"=>WilsonPositionPrescribedFrame.positioned U J N.store
local notation "Φ"=>WilsonPositionHomogeneousFrame.homogeneous U J N
include lead H
-- also follows from `continuum_rows` using uniform/smul; here specialized to the *exact original proposition* and can use non-LogTrace.
theorem same_frame_through (H₀:Batch.Pose U W N t){K:Set (Points n)}(hK:IsCompact K)(hx:K⊆conf n)(v:Fin n→Sec G h)(q:ℕ):
    matchesThrough N M U J ν h v K q:=by
 let A:= Scale.Measure.outlook N.scheme N.criterion
 intro ε he; let he' : Receives t trail (fun r (x:↥K)=> frank U Φ none h r x.val v) (fun x=> sent A h x.val v):= Batch.YPose U W Φ N M H H₀ (earning U J N M H lead H₀.running) K hK hx v
 obtain ⟨C,hC,hP⟩:= (he'.good q).cost
 let e:= (Coupling.conforms hG H₀.running).abs.const_mul C; rw [abs_zero,mul_zero] at e
 filter_upwards [e.eventually_le_const he,hP] with r ht hr x hz; have hv : WilsonPositionHomogeneousComparison.observed N U J h v r x.val=frank U Φ none h r x.val v:= rfl
 rw [hv,show WilsonPositionHomogeneousComparison.polynomial N M ν h x v q (t r)= appointedH140Crop q (t r) (sent A h x.val v) from ?_]
 · refine (hr ⟨x.val,hz⟩).trans ( (le_of_eq (show C * |t r|^(q+1)=C * |t r| * |t r|^q by ring)).trans (mul_le_mul_of_nonneg_right ht (by positivity)))
 unfold WilsonPositionHomogeneousComparison.polynomial; rw [crop_eq]; apply Finset.sum_congr rfl; intro i _; rw [cashed A _ x.property, WilsonPositionHomogeneousComparison.filed N M H]
end YM.Integration.GradedFar
