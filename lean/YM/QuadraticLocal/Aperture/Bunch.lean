import YM.QuadraticLocal.Aperture.Ram
import YM.QuadraticLocal.Sunrise.Fruit
import YM.QuadraticLocal.Aperture.Lyre
/-!
 # DUMMY bundle of anchored mark operands
 Keep δ sample for every α slot. Distinct symbols used BEFORE combining polynomial nilpotents
 on common Θ. A later push certificate will read ALL markers together, with every Board point
 supported. Remove mask harm in `LaneSplit`; this is telescope, not claim of true aux good for lift.
-/
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
variable {G:Gauge} {L n f: Side}{ι V: Type} [Fintype V][DecidableEq V] {W b D α a B C Ω κ V₀:ℝ}{k p M:ℕ}
variable {P:Patch}{K:KernelChoices}{S : StepData n f} {s:Teller G}{η : Stage}
open Metric ConnectedActivityE6.Coat
open Till Tilt Lantern Aux Aux.Name
namespace Bunch
variable (I:V→Loan)(u:∀ i, Atom G (I i).r)(α:V→Site n→ Site f)(x:V→Site n)
local notation "φ"=> V→ℝ
-- directions.stencil support ALL atomic placements.Pin support born from Γ.K.Ω.Roots.
def mapC : rule V n:= fun p=> if p.1=x p.2 then 1 else 0
local notation "loc" i=> α i (x i)
local notation "Vc"=>mapC x
variable (v: V→ℝ)
def beamF (i:V)(t:ℝ)(V':Config G f):= t^((I i).stamp+1)*(u i).unmasked V' (loc i)
def beam (t:ℝ) : Config G f→ℝ:= ∑ i:V,(-v i) • beamF I u α x i t
lemma cover (t:ℝ): RG.Envelope (beam I u α x v t):=by rw [show beam I u α x v t=(fun y=>∑ i:V, (-v i)*beamF I u α x i t y) from funext fun y=> Finset.sum_apply ..]; exact RG.Envelope.sum _ _ (fun i=>(RG.Envelope.const _).mul ((RG.Envelope.const (t^((I i).stamp+1))).mul ⟨(u i).unmasked_cont (loc i)|>.measurable,_,fun z=>(u i).unmasked_bound z (loc i)⟩)) -- replace
-- Fix the forest and its associated configuration spaces.
variable (F:Forest S.ratio)
local notation "Y"=> Body (Precision.Key F G)
local notation "X"=> Apex n G × Body (Precision.Key F G)
local notation "E"=> ℝ×(Apex n G × Body (Precision.Key F G))
local notation "u₀" i=> Loan.leafMatter (I i) (u i) (α i (x i)) F
local notation "Φ" i:max=> Aperture.scene F (beamF I u α x i)
local notation "Σ₁"=> Aperture.scene F (beam I u α x v)
local notation "T0" i:max=> -(v i)
lemma adept (i:V) : Rise (Φ i):= by
 let U:= u₀ i; have ht(e:E): (Φ i) e=e.1^((I i).stamp+1)*U e.2:=rfl; have hh:= Loan.healthy (I i) (u i) (loc i) F; let p':= (I i).stamp+1; let d':= (I i).e+(I i).toll+2; have he:= (I i).recovery; have hj:= (I i).higher; exact ⟨(contDiffAt_fst.pow p').mul (ContDiffAt.comp (g:=U) (f:=Prod.snd) (0:E) hh.smooth contDiffAt_snd),fun j hj'=>funext fun v=> (Floe.favor_pocket U hh.smooth d' (I i).r p' j hh.vanish v.1 v.2 (by unfold d' p'; omega) (by unfold d'; omega))⟩
lemma jet_scale {X':Type}[NormedAddCommGroup X'][NormedSpace ℝ X'] (g:X'→ℝ)(a:ℝ)(h:ContDiffAt ℝ ω g 0)(k:ℕ)(y:X') : jet (a • g) k y = a • jet g k y:=by
 unfold jet; rw [iteratedFDeriv_const_smul_apply (h.of_le le_top)]; change (Nat.factorial k:ℝ)⁻¹ * (a* _)= _; rw [smul_eq_mul]; ring_nf; rfl
lemma esteem : Rise Σ₁:= by
 let f i:= Φ i; have h i:= adept I u α x F i; have ht : Σ₁=∑ i:V, (-v i) • f i:=by ext1 x; unfold Aperture.scene beam; simp only [Finset.sum_apply]; rfl
 rw [ht]; have he i: ContDiffAt ℝ ω ((-v i) • f i) 0:= (h i).nice.const_smul (-v i); refine ⟨?_,fun k hk=>?_⟩
 · rw [← show (fun y=>∑ i:V, (-v i) • f i y)=∑ i:V,(-v i) • f i from funext fun y=> (Finset.sum_apply y univ (fun i:V=> (-v i) • f i)).symm]; exact ContDiffAt.sum fun i _=> he i
 ext1 x; rw [goth (fun i _=> he i)]; apply Finset.sum_eq_zero; intro i _; rw [jet_scale _ _ (h i).nice, (h i).ranks k hk]; exact mul_zero _ -- names
end Bunch
end YM.QuadraticLocal.Aperture
