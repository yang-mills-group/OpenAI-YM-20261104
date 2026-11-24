import YM.Qlocal.Canopy.Audero
import YM.Qlocal.Canopy.Port
/-!
 # Spectrum: honest auxiliaries (Caliper worked at physical beta & same θ forecast).
 Price agreements on both sectors, carefully before keeping masks. T is not the physical time;
 analytic receipt extends (Probe-uniform) tickets through sequences. Projection is with FULL
 inputs; exact log estimate after analytic crops with **independent admissible price**.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Bind
open Function Filter Set Metric Lattice MeasureTheory ProbabilityTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid
open AllOrder Ker Laplace Laplace.SigmaP Response Catch
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open Marker Multi PertExtension.Series Radial Extra.Iteration Floe PositionX.Jet
open Comparison.RG02.Order
open Comparison.RG02.Assembly
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {k j i q q' r:ℕ} {n c f :Side}{S:StepData c f} {b α t:ℝ}
namespace Aurum
open PertExtension PertExtension.Series Sienna Lantern Catch Catch.Clock tether
open Canopy Lithe
variable {ι:Type*}{S':Catch.Clock ι}{P:Patch}{T:KernelChoices}{v:Stage}{u:ℝ→ℝ}{κ:ℕ}{F:Uniform.Before G v.width v.paths P.J T (k+3+3)}
open Aux.Name Presented Poll
variable (O:ChartRatio G)(hO:LocalRatio O) (D:ℝ)
local notation "I"=>Aux.Name G P T u κ v (k+3) F
-- actual denominator* & model thermal projection. binder
section prelim
variable (Q : Aux.Name G P T u κ v (k+3) F) {R R' K : reed G Q.f} {b:ℝ}
variable {s : Age→ℝ} (h:Q.Civil s)
local notation "M"=> Q.tilt.eval
local notation "Δ"=> Q.data.push Q.beta
variable (hR:Flute R q) (hR':Flute R' q) (hh:K=R+b • R')
include h hR hR' hh
lemma variations : actual Q K q= actual Q R q+ b • actual Q R' q:= by
 let t:= Q.Θ; let f:=marked Q R q; let g:=marked Q R' q; have hg : M*marked Q K q=M*f+ b • (M*g):= by subst K; ext1 i; change M i * ((t^q)⁻¹ * (R t i+b*R' t i)) = M i*((t^q)⁻¹ * R t i) + b*(M i*((t^q)⁻¹ * R' t i)); ring
 ext1 x; unfold actual; rw [hg,StepData.push_add (Q.data.isKernel Q.loom.large.1 _),Pi.add_apply]; swap
 · obtain ⟨p,hp,hH⟩:= h.price; exact ((Q.tilt.envelope hH.cap).mul ((Envelope.const _).mul (hR.envelope _))).integrable _
 swap; · obtain ⟨p,hp,hH⟩:= h.price; exact (((Q.tilt.envelope hH.cap).mul ((Envelope.const _).mul (hR'.envelope _))).integrable _|>.smul _)
 rw [push_linear Q R' hR' h]; change ((Δ (M*f) _)+ b * (Δ (M*g) _))/_= Δ (M*f) _ / _+ b*(Δ (M*g) _/_); ring -- include hR' h
end prelim
variable (W:ι→ Aux.Name G P T u κ v (k+3) F) (K K': Horn.ListV W) (hW: Aux.Name.Proper W S')
variable {p:ι→ℝ}{x:∀ i,(W i).X}(ht : ∀ᶠ i in S'.rail, (W i).goods O D (p i) (x i))(hv:S'.Meter p 0)(hp:(S').Meter (fun i=> ‖x i‖) (-(1/2))) (hD:0<D)
variable (d:ι→ℝ)(hd:S'.Meter d (graded 1))(hx:∀ᶠ i in S'.rail,0<d i)
set_option quotPrecheck false
local notation "ε"=> fun i:ι=> (d i)⁻¹
local notation "R"=> fun i:ι=> (W i).Θ
local notation "LT"=> Lithe.Sail S' R ε j r
local notation "P0"=> S'.rail
include hW ht hv hp hD hd hx
variable (hk:Version G P.L j k q r)
include hk hO
lemma renewable (hR:Horn.Lane W K S' (k+3) q) : LT (fun i=> model (W i) (K i) O hO (hR.tells i)) (fun i=>actual (W i) (K i) q) x:= by
 have hu:= hW.meter W|>.1; refine Lithe.Sail.sails hu (hx.mono (fun i hi=> inv_nonneg.mpr hi.le)) _ (?_) ?_
 · intro b he; exact spool O hO D W K hR hW ht hv hp hD j b (by have hv:= hk.born; omega) d (hd.weak (by simp [graded])) hx
 exact echelons O hO D W K hR hW ht hv hp hD hk d (hd.weak (by simp [graded])) hx
variable {c':ι→ℝ} (he:S'.Meter c' (graded (r+1)))
include he hk
lemma clipped (hc:Horn.Shrunk S' (k+3) q c' K K') : LT (fun i=> model (W i) (K i) O hO (hc.1.tells i)) (fun i=>actual (W i) (K' i) q) x:= by
 let h:= renewable O hO D W K hW ht hv hp hD d hd hx hk hc.1
 obtain ⟨L,hL,H⟩:= hc.2; apply (h.hire); have ht:= renewable O hO D W L hW ht hv hp hD d hd hx hk hL; obtain ⟨r,hP,H'⟩:= hW.legible; apply (ht.total.caliber he).weak (by simp)|>.home; filter_upwards [H'] with i hi; have hv:actual (W i) (K' i) q= _:= variations (b:=c' i) _ hi (hc.1.tells i) (hL.tells i) (congr_fun H i); rw [hv,add_sub_cancel_left] -- right? direction
-- apply to arbitrary collection X.Produce.T.Frame. hours
end Aurum
end YM.Qlocal.Bind
