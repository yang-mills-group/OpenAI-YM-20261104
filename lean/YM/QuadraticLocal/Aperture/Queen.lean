import YM.QuadraticLocal.Aperture.Gallery
import YM.AllOrder.Wheel.Travel
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Aperture
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder PertExtension PertExtension.Series AllOrder.Laplace AllOrder.Laplace.SigmaP Response Laurent Stationary
open PositionX.Jet Extra.Iteration AllOrder.Floe AllOrder.Floe.Pace AllOrder.Floe.Aero AllOrder.Floe.StateE
open AllOrder.Catch AllOrder.Catch.Clock Sienna
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Ink Marker Sunrise Toggle Radial
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge}{ι:Type*}{T:AllOrder.Catch.Clock ι} {D a B C Ω κ v:ℝ}{k p m x:ℕ} {V:Type}[Fintype V][DecidableEq V]
variable {P:Patch}{K:KernelChoices}{s:Teller G}{r:Stage}{q:ℝ→ℝ}{U:Push.Uniform.Before G r.width r.paths P.J K ((k+3)+3)}
open Metric ConnectedActivityE6.Coat
open Till Tilt Lantern Aux Aux.Name
namespace Page
variable (W : ι → Aux.Name G P K q x r (k+3) U) (M: V→Loan) (A:∀ i,Page (W i) M) (h:Aux.Name.Proper W T)
variable {O:ChartRatio G}(hO:LocalRatio O)
set_option quotPrecheck false
local notation "FI" i=> (W i).Fs
set_option quotPrecheck false
local notation "P₀" i=> (W i).X
local notation "Φ" i=> (W i).Θ
local notation "QΩ"=> (fun i t=> Page.nozzle (W i) M (A i) t)
local notation "Y"=> Drawer.Knife V
local notation "Z"=> Crew V
variable {y z:∀i,(W i).X}(pH:ι→ℝ)
-- Cert for all stationary caps from atom budget.Epoch.Scope.ρ.WidthB.
variable (hv:0<a)
local notation "Ψ" i:max j:max=> Loan.leafMatter (M j) ((A i).mark j) ((A i).path j ((A i).root j)) (FI i)
local notation "b₀" i:max j:max=> ((A i).mark j).budget a
local notation "Rt"=> T.rail
local notation "H*"=> fun i => ((W i).X × Body (Precision.Key (W i).forest G))
variable (L:∀ j:V,T.Meter (fun i=> ((A i).mark j).budget a) 0)
include hv L
lemma room (j:V) (n:ℕ)(x:∀ i,(W i).X × Body (W i).Vx)(hx:∀ᶠ i in T.rail, ‖x i‖<1): Catch.Cover T n 0 (fun _=>1) (fun i=> Ψ i j) x:= Function.const _ (Function.const _ (by
 obtain ⟨v,h⟩:= paint_supply G n; let H i:= b₀ i j * Uniform.atomCost G v a n (M j).r; -- H notation
 refine Catch.Cover.has ((L j).rscale (Uniform.atomCost G v a n (M j).r)) ?_; filter_upwards [hx] with i hx; let F:= (W i).forest; let r:= combineH F (G:=G); let p:= r (x i); have hr:=feesComb F (G:=G); let z:=(A i).path j ((A i).root j); let u:=(A i).mark j
 obtain ⟨C,hp,hC⟩:= pay_atom F 1 h p ((r.toContinuousLinearMap.le_opNorm (x i)).trans ((mul_le_of_le_one_left (norm_nonneg _) hr).trans hx.le)) z u hv
 unfold signedFine at hp; simp_rw [pull_id] at hp; let f y:= u.unmasked (fine G F y) z; have h' : Brush n C 1 (f∘r) (x i):= by
    have ht:= Brush.reading r.toContinuousLinearMap (show Brush n C 1 f p from Brush.offer.mpr ⟨ hp.analytic.of_le le_top ,hp.norm_le⟩) hr; rw [one_mul] at ht; exact ht
 exact h'.climb ((le_mul_of_one_le_right hp.nonneg (Real.one_le_exp (mul_nonneg (width_positive hv ..|>.le) (by positivity)))).trans hC) le_rfl -- `u`
  ) (inferInstance : Fintype V)
  ) (inferInstance : DecidableEq V)
include h
set_option maxHeartbeats 200000 in
lemma gas_mark (n:ℕ)(x:∀ i,ℝ×((W i).X × Body (W i).Vx))(hx:∀ᶠ i in T.rail, ‖x i‖<1) (t:V→ℝ) : Catch.Cover T n 0 (fun _=>1) (fun i=> Phase.roofP (W i) (Page.nozzle (W i) M (A i) t)) x:=by
 let V':= H*; let Z' i:= ContinuousLinearMap.fst ℝ ℝ (V' i); let s i:= ContinuousLinearMap.snd ℝ ℝ (V' i); have ht:T.Meter (fun i=> ‖x i‖) 0:= Clock.Meter.smaller (Clock.Meter.const T 1) (hx.mono (fun i hi=> (abs_of_nonneg (norm_nonneg _)).trans_le (hi.le.trans (le_abs_self _))))
 have hb: Catch.Cover T n 0 (fun _=>1) (fun i=> ⇑(Z' i)) x:= by refine (Catch.Cover.comp_lin («L»:=Z') (s:=0) ht le_rfl ?_).weak (by simp); exact (Clock.Meter.const T 1).smaller (Eventually.of_forall fun i=> (abs_of_nonneg (norm_nonneg _)).trans_le ((ContinuousLinearMap.norm_fst_le ..|>.trans (le_abs_self _))))
 have hS: Catch.Cover (U:= V') T n 0 (fun _=>1) (fun i=> ⇑(s i)) x:= by refine (Catch.Cover.comp_lin (L:=s) (s:=0) ht le_rfl ?_).weak (by simp); exact (Clock.Meter.const T 1).smaller (Eventually.of_forall fun i=> (abs_of_nonneg (norm_nonneg _)).trans_le ((ContinuousLinearMap.norm_snd_le ..|>.trans (le_abs_self _))))
 let z i:= s i (x i); let f (j:V) i:= (-t j) • Aperture.scene (W i).Fs (Bunch.beamF M (A i).mark (A i).path (A i).root j)
 have hp j: Catch.Cover T n 0 (fun _=>1) (f j) x := by
     have hi:= (Catch.Cover.comp (u:=fun i=> Ψ i j) le_rfl hS (room W M A hv L j n z (hx.mono fun i hi=> (norm_snd_le _).trans_lt hi))); let X':= (M j).stamp+1; have hy: Catch.Cover T n 0 (fun _=>1) (fun i=>Aperture.scene (W i).Fs (Bunch.beamF M (A i).mark (A i).path (A i).root j)) x:= by exact ((Catch.Cover.mul (V:=fun i=>ℝ×V' i) (hb.powerC X') (hi.weak (b:=0) (by simp))).weak (by simp));
     exact ((Catch.Cover.caliber hy (Meter.const T (-t j))).weak (by simp))
 have H₁:= Catch.Cover.add (Aux.Name.Proper.gas W h n x hx) (Catch.Cover.collects (f:=f) _ (fun i (_:i∈univ)=> hp i))
 refine Catch.Cover.home H₁ (Eventually.of_forall fun i=>?_ ); unfold Phase.roofP nozzle; simp only [Finset.sum_apply, Bunch.scene_eq]; rfl
lemma salary (t:V→ℝ) : Flood (X:=fun i=>(W i).X) («Y»:=fun i=>(W i).Vx) (fun i=> Phase.roofP (W i) (Page.nozzle (W i) M (A i) t)) T (k+3):=by
 refine ⟨Eventually.of_forall fun i=> Phase.raised _ _,fun e he=>?_⟩; let V i:= Metric.ball (0:ℝ × H* i) 1; let p:=T.book V; let O':= T.bookF V;
 have hh: Catch.Cover (T:=p) (V:=fun i=> ℝ× (H* i.1)) (U:=fun _=>ℝ) (k+3) 0 (fun _=>1) (fun i => Phase.roofP (W i.1) (Page.nozzle (W i.1) M (A i.1) t)) (fun i=> i.2.1):= gas_mark (T:=p) (W∘Sigma.fst) M (fun i=> A i.1) (Aux.Name.Proper.sail W h _ _ O') hv (fun j=>(L j).pays Sigma.fst O') (k+3) (fun i=>i.2.1) (Eventually.of_forall fun i=> mem_ball_zero_iff.mp i.2.2) t
 filter_upwards [T.booked V (fun i x=> Brush (k+3) (T.cost i^e) 1 (Phase.roofP (W i) (Page.nozzle (W i) M (A i) t)) x)|>.mp (hh e he)] with i hi; exact fun x hx=> hi x (mem_ball_zero_iff.mpr hx)
end Page
end YM.QuadraticLocal.Aperture
