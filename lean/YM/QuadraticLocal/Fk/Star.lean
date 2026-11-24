import YM.QuadraticLocal.Fk.Unit
import YM.QuadraticLocal.Fk.Table
import YM.QuadraticLocal.Fk.Maps
/-!
# Exact Fk equality to projection on all finite names

No identification with cover here; this is finite-volume exact algebraic formulation.
Need to use for any legal finite subquery prior to assembly. The issued momentum
frames are at ALL marker names and full supports (of predictor tree). Costs only after
summing kernels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration AllOrder.Catch AllOrder.Catch.Clock AllOrder.Floe AllOrder.Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {V:Type}{G:Gauge} {n c:Side} {k j d r:ℕ} {a b σ :ℝ}
open Aperture Poetry Echo Work.G05 Toggle Aux Aux.Name Marker Multi
open QuadraticLocal.Sunrise
variable {ι α : Type} [DecidableEq V] {P:Passport n V} {R:Census V}
variable (M:ι→ Row P R G α)
variable (F: Finset ι) (L:Layout G) (T:Finset Age)
namespace ScatterR
set_option quotPrecheck false
local notation "R₀"=> Focus.census ι
open Comparison.RG02
open Marker Multi
-- ℝ colors are powered mark functions for Fk, have denominator.
section mix
variable {V₁:Type} [DecidableEq V₁](J:Census V₁)(e:ι→Multi.Hot J)(q:ι→ℂ) (w:V₁→ℕ)
local notation "Yₐ"=> Launch.index J w

local notation "Pℓ"=> ScatterR.colors M F L T J e q w
variable {c' : Side} {S:StepData c' n} {B₀:Clip} {D':PathData G}{O:ChartRatio G}
open Comparison.RG02.Bulk
variable (K:Comparison.RG02.Bulk.Kernel S B₀ D' O)(X:Forest S.ratio)(t:S.Choices)(x:Exterior.fieldDir G c' 1)
set_option quotPrecheck false
local notation "ℳ"=> Bulk.Joint S X (G:=G)
local notation "Z"=> BoardL c _ _ -- not needed
variable (H: ∀i∈F,(M i).lamp.toll = Launch.index J w (e i).val)
local notation "δ"=> (fun i:ι=> (M i).lamp.toll)
local notation "G0" h:max=> Bulk.markFn S X h
local notation "n₀"=> (fun i:ι=> (M i).lamp.power)
local notation "fc" q:max p:max=> Bulk.posed S X (familyAt M q p)
variable (p':Multi.Hot J)
local notation "S'"=> (F.filter (fun j:ι=> p'.val=(e j).val))
variable (v:Bulk.Joint (G:=G) S X)(i:ℕ)
include H
lemma lit_at : Assembly.markLetter (Pℓ).power (Bulk.markFn S X (Pℓ)) p' v i= ∑ j∈ F.filter (fun j'=> p'.val=(e j').val), Assembly.jet (Bulk.posed S X (familyAt M q j)) ((M j).lamp.power+i) v:= by
 let f(j:ι):= Bulk.posed S X (familyAt M q j); have h j:ContDiffAt ℝ ω (f j) 0:= (Bulk.joint_receipt S X (ScatterR.mature M q j)).smooth
 have hh: (G0 (Pℓ)) p'=∑ j∈S', f j := by funext v; unfold markFn posed; rw [markEq]; simp_rw [Finset.sum_apply]; rfl -- parse G0
 unfold Assembly.markLetter; rw [hh]; nth_rw 1 [Assembly.jet]; rw [iteratedFDeriv_sum_apply (fun j _=> (h j).of_le le_top),_root_.sum_apply,Finset.smul_sum]; exact Finset.sum_congr rfl (fun j h=> by rw [show (Pℓ).power p'=(M j).lamp.power from congr_arg (·+1) ((congr_arg (Yₐ) (mem_filter.mp h).2).trans (H j (mem_filter.mp h|>.1)).symm)])
local notation "G'"=> ScatterR.lit_at
-- one assembly coefficient at power d. power-right.Route linear over projector assignments.
lemma wave : PowerSeries.coeff i (Assembly.affine (Pℓ).power (Bulk.markFn S X (Pℓ)) (Bulk.geometric K X t (Pℓ)) v)= Poly.bead J (Complex.ofReal (Assembly.vacuumLetter (Bulk.geometric K X t (Pℓ)) v i)) + ∑ j∈F, Poly.send (e j).val (Assembly.jet (Bulk.posed S X (familyAt M q j)) ((M j).lamp.power+i) v):= by
 rw [Assembly.affine,map_add,Assembly.realCoeff,Assembly.curve,PowerSeries.coeff_mk]; congr 1; apply Marker.Poly.ext; intro i'; rw [Poly.part_sum]; by_cases he:i'=J.quiet;
 · subst i'; simp_rw [part_lit_quiet,part_quiet_hot,Finset.sum_const_zero]
 let k':Multi.Hot J:= ⟨i',(Cumulants.hot_iff_ne _).2 he⟩; rw [show (lit J (fun x=> Assembly.markLetter _ ( G0 (Pℓ) ) x v i)).part i'= _ from part_lit _ k',lit_at]; rotate_left; · exact H
 simp_rw [Finset.sum_filter, Poly.part_send]; rfl
omit H
lemma translates (i₁:ι) : Assembly.jet (Bulk.posed S X (familyAt M q i₁)) i v = q i₁ * Assembly.jet (Bulk.posed S X (familyAt M (1:ι→ℂ) i₁)) i v:= by
 let f:= Bulk.posed S X (familyAt M (1:ι→ℂ) i₁); let F:ℂ→L[ℝ]ℂ:= q i₁ • ContinuousLinearMap.id ℝ ℂ; have he:Bulk.posed S X (familyAt M q i₁)= F ∘ f:=by funext v; dsimp [Bulk.posed,familyAt,F,f]; simp
 rw [he]; exact (Assembly.jet_apply_left F f _ ((Bulk.joint_receipt S X (ScatterR.mature M _ i₁)).smooth.of_le le_top) _).symm
local notation "T₁"=> Bulk.stage K X x
variable [DecidableEq ι][Fintype ι][Fintype V₁]
local notation "W'"=> ν₂.Payment -- not used
local notation "r0"=> F
-- mapping from basis execution to actual.CHR connectors
local notation "Y0"=> (Focus.census ι)
def gems (i:ι): Poly J:= Poly.send (e i).val (q i)
omit [DecidableEq ι] [Fintype ι] in
lemma gnil (i:ι): gems J e q i * gems J e q i=0:= by rw [← sq,gems,Focus.no_merge] -- square syntax
local notation "Λ"=> TableMap.mapC (ScatterR.gems J e q) ( ScatterR.gnil J e q )
local notation "ϛ"=> (ScatterR.edition M F L T)
local notation "W"=> Pℓ
local notation "φ₀" v:max=> (Assembly.affine (ζ).power (Bulk.markFn S X (ζ)) (Bulk.geometric K X t (ζ)) v)
-- h authentic already from H lanes.V.E.C.Shape.Meta.En.Expr`
include H
lemma comparison : PowerSeries.map (Λ).toRingHom (Assembly.affine (ϛ).power (Bulk.markFn S X (ϛ)) (Bulk.geometric K X t (ϛ)) v)= Assembly.affine (Pℓ).power (Bulk.markFn S X (Pℓ)) (Bulk.geometric K X t (Pℓ)) v:= by
 let w':ι→ℕ:= fun i=>(M i).lamp.toll; have he i : (M i).lamp.toll=Launch.index (Focus.census ι) w' (Focus.detailI i).val:= (Focus.weight w' i).symm; ext1 k; unfold edition; rw [PowerSeries.coeff_map,ScatterR.wave M F L T _ _ _ _ K X t (fun i _=> he i), ScatterR.wave M F L T _ _ _ _ K X t H, _root_.map_add, _root_.map_sum]; -- argument order using #check
 congr 1; · exact (Λ).commutes _
 refine Finset.sum_congr rfl fun i hh=>?_; rw [translates M q X v _ i]; -- sig
 exact (TableMap.primitive (gems J e q) (gnil J e q) i _).trans ( (send_scale _ _ _).symm.trans (congr_arg _ (mul_comm ..)))
-- moment equality. Keep height parameter: version.Auth.Me.Scope.Frame
include x
local notation "Ψ" C':max=> (Bulk.Fk K X t C' x)
lemma transmission (d k:ℕ): Order.observe J k (Order.logMarked ( (Ψ (W)) k)) d= (TableMap.mapC (ScatterR.gems J e q) (ScatterR.gnil J e q)) (Order.observe (Focus.census ι) k (Order.logMarked ( (Ψ (ϛ)) k )) d):=Morph.inspection Λ (fun x=> TableMap.unmarked (gems J e q) _ x) K X _ _ t x (fun v=> comparison M F L T J e q w K X t H v) d -- argument
end mix
end ScatterR
end YM.QuadraticLocal.Earn
