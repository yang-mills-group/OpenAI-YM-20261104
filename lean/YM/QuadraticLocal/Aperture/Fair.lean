import YM.QuadraticLocal.Aperture.Queen
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
variable {r':ℝ}
set_option quotPrecheck false
local notation "K₁"=> (fun i=> Page.portion (W i) M (A i))
local notation "X₁"=> (fun i=> (W i).price)
local notation "d*"=> ((fun i=> (W i).Θ))
-- endemic if flag.D.th power even with long-support.Note.Th width.Extra.Chapter.B.Budget.R. cap uses positive grade e.
abbrev salaryR (a:ℝ)(j:V)(i:ι):= let u:=M j; let v:=(W i).Θ; (v⁻¹)^u.power*v^u.stamp*((A i).mark j).budget a*(W i).price.threshold^u.r
local notation "W'"=> salaryR W M A a
variable (j:V)
include hv
lemma oldR (i:ι) (x:Config G (W i).f) (he:flags (W i).price.threshold x=∅): ‖K₁ i j x‖≤ W' j i:=by
 unfold Page.portion Loan.letter; simp_rw [norm_mul,norm_pow,norm_inv,norm_pow,Real.norm_of_nonneg (Name.Θp _).le]; let p:=(W i).price; let F:=(A i).mark j; let u:=(A i).path j ((A i).root j)
 let w:= healthy_atom F p x u; have hh : Healthy p.threshold (F.footprint u) x:=by unfold Healthy; rw [show flags p.threshold x=∅ from he]; simp; -- fix annotation
 unfold Atom.placed at w; rw [masked_eq _ _ _ _ hh] at w; let s:=(W i).Θ; let r:=(M j); let a':=(s⁻¹)^r.power; let b:=s^r.stamp; have hp:0<s:= Name.Θp _; rw [← inv_pow]; change a'*(b*_ ) ≤ a'*b*_ * _; rw [← mul_assoc a'] -- precedence maybe annotate
 exact mul_le_mul_of_nonneg_left (w.trans (mul_le_mul_of_nonneg_right (F.lower_budget _ hv) (pow_nonneg p.threshold_pos.le _))) (by unfold b a'; positivity)|>.trans_eq (mul_assoc ..|>.symm) -- wrong dir
include L h
omit hv in
lemma earnedP : T.Meter (W' j) (graded (M j).e):= by
 obtain ⟨h₁,h₂⟩:= Proper.meter W h; let p:=M j; refine (((((h₂.pow p.power).mul (h₁.pow p.stamp)).mul (L j)).mul ((Proper.cheap W h).pow p.r)).weak ?_); have hh: p.stamp+p.r=p.power+p.e:=by rw [p.recovery]; unfold Loan.power; omega
 unfold graded; let K':Loan:= p; change _ ≤ -(1/2:ℝ)*p.e; have hx:= Nat.cast_inj (R:=ℝ) |>.2 hh; unfold Loan.power; push_cast at hx ⊢; linarith
lemma castsR (v:V→ℝ) : ∃ f:ι→ℝ,T.Meter f 0 ∧ ∀ i (x:Config G (W i).f), flags (W i).price.threshold x=∅ → ‖Sage.member (Page.portion (W i) M (A i)) (v,x)‖≤ f i:= by
 let f i:= ∑ j:V, ‖v j‖*W' j i; refine ⟨f,Meter.sum univ ?_,fun i x hx=>(norm_sum_le ..).trans (Finset.sum_le_sum ?_)⟩
 · intro i hi; exact ((earnedP W M A h L i).lscale (‖v i‖)).weak (by unfold graded; linarith [Nat.cast_nonneg (α:=ℝ) (M i).e])
 intro j hj; exact (norm_mul (v j) _).trans_le (mul_le_mul_of_nonneg_left (oldR W M A hv j i x hx) (norm_nonneg _))
lemma hygienic : Habitat W M A T:= by
 refine ⟨fun i=> salary W M A h hv L (Toggle.convertS i),fun i=>?_⟩; obtain ⟨f,hf,hw⟩:= castsR W M A h hv L (Toggle.convertS i); exact ⟨f,hf,Eventually.of_forall hw⟩
end Page
end YM.QuadraticLocal.Aperture
