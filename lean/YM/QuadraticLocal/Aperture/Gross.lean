import YM.QuadraticLocal.Aperture.Fair
/-!
 # Real-chart derivatives through Gram & interpolation. First gross

 Don't divide by the conditional mass without checking the payment! Here on the little auxiliary
 one can do it at a cost (kernel weighted-derivative inequality gives common weight/cap),
 before full Space.H labelling. It's NOT OK to lift that gross ratio polynomial on its own,
 only lift the announced *discrepancy* with its weights on the actual path.Middle.True.
 Body seeds & Mark polynomial still all to be costed. Gross paid for S*C Plot.Eptr, not universal ζ.
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
variable {G:Gauge}{ι:Type*}{T:AllOrder.Catch.Clock ι} {D a B C Ω κ v:ℝ}{j k n m x:ℕ} {V:Type}[Fintype V][DecidableEq V]
variable {P:Patch}{K:KernelChoices}{s:Teller G}{r:Stage}{q:ℝ→ℝ}{U:Push.Uniform.Before G r.width r.paths P.J K ((k+3)+3)}
open Metric ConnectedActivityE6.Coat
open Till Tilt Lantern Aux Aux.Name Token
namespace Gross
variable (A : Aux.Name G P K q x r (k+3) U)
local notation "μ"=> A.forest.order G
local notation "Θ"=> A.newZ
set_option quotPrecheck false
local notation "Z'"=> A.forest.Slice G
local notation "Ω"=> A.X
local notation "F"=> A.Fs
local notation "b"=> A.beta
variable {s:Age→ℝ} (h:A.Civil s) (ξ:A.forest.Slice G →ℝ)(hp: PaintSupply G j v) {V' M:ℝ} (hz: Brush j C 1 Real.exp 0)
local notation "q₀"=> prime G A.data.kernel j v C A.beta B
variable (hc:(Fintype.card (Bond A.c):ℝ) ≤ B) (he:0≤ prime G A.data.kernel j v C A.beta B)
-- normalized per point w mass TRUE. Warranty.Must cost. ξ may be packing-stencil products.W makes no claims off event, location through s wanted.
variable (x:A.X)(hx: ‖x‖<1)(hQ:Envelope ξ)(hW:∀ i, A.newZ x i≠0→ ‖ξ i‖≤ M)  (hm:0 ≤ M)
include h
lemma halo : ∃ C:ℝ,0 ≤ C∧ ∀ x i, A.newZ x i ≤ C:=by
 have ht₀:= A.loom.large.1; obtain ⟨p,hP,hQ⟩:= h.price; have h₀ f:0 ≤ A.tilt.eval f:= by rw [A.tilt_eq]; apply mul_nonneg _ (Real.exp_pos _).le; change 0 ≤ (Pane.virgin _ _ _).eval _; rw [Pane.sparkling]; split<;> positivity
 obtain ⟨r₀,hr⟩:= A.data.density_bound ht₀ A.beta; obtain ⟨t₁,hv⟩:= (A.tilt.envelope hQ.cap).cost; refine ⟨|r₀| * |t₁|,mul_nonneg (abs_nonneg _) (abs_nonneg _),fun y i=>?_⟩
 let f:= (F).drape i; have he : A.newZ y i= A.data.density b f (Desk.night y)* A.tilt.eval f:= by rw [A.tilt_eq,← mul_assoc]; exact congr_arg (· * Real.exp (A.view f)) (Fare.total ..)
 rw [he]; exact mul_le_mul ((hr _ _).trans (le_abs_self _)) ((le_abs_self _).trans ((hv _).trans (le_abs_self _))) (h₀ _) (abs_nonneg _)
def heat (x:A.X):ℝ:=∫ i, A.newZ x i * ξ i ∂A.forest.order G
abbrev boundX (x:A.X):ℝ:=heat A ξ x / A.attends x
include hp hz hc he hQ hx
local notation "t"=> q₀
private lemma title (y:A.X)(hy : ‖y‖≤ 1)(i:A.forest.Slice G): Brush j (q₀*A.newZ y i * ‖ξ i‖) 1 (fun x=> A.newZ x i *ξ i) y:=
 (((tilted_brush A h hp hz hc _ hy i).smul (ξ i)).shimmy (Eventually.of_forall fun x'=> mul_comm ..)).climb (le_of_eq (mul_comm ..)) le_rfl
-- Alignment doesn't pay on AUX from virtual Prog:E.K. Formal.At this Stage. Need register actual WarmLog.Cost.Mode.
include hm hW
lemma film : Brush j (q₀*M*A.attends x) 1 (heat A ξ) x:= by
 let N:=A.forest.order G; let f:=fun y i=> A.newZ y i*ξ i
 let Y y:= A.tilt_record h y; have ht: Meristem f x N j:= by
     obtain ⟨U',hU,hV⟩:=halo A h; obtain ⟨W,hT⟩:= hQ.cost; let Z:= (q₀)*U'*|W|
     apply (Meristem.points f N ?_ (Eventually.of_forall fun i=>((Y i).2.1.mul hQ).meas)).1; refine ⟨fun i=>Z,integrable_const _,(continuous_norm.continuousAt.eventually (gt_mem_nhds hx)).mono fun y hy i=>?_⟩
     exact (title A h ξ hp hz hc he x hx hQ y hy.le i).climb (mul_le_mul (mul_le_mul_of_nonneg_left (hV y i) he) ((hT i).trans (le_abs_self _)) (norm_nonneg _) (mul_nonneg he hU)) le_rfl
 let g i:= q₀*M*A.newZ x i; have he' i:t*A.newZ x i* ‖ξ i‖ ≤ g i:= by by_cases hi:A.newZ x i=0
                                                                      · unfold g; simp [hi]
                                                                      exact (mul_le_mul_of_nonneg_left (hW i hi) (mul_nonneg he ((Y x).1 _|>.1))).trans_eq (mul_right_comm ..)
 exact ht.buds g ((Y x).2.1.integrable N|>.const_mul _) zero_le_one (by unfold g; rw [integral_const_mul, (Y x).2.2.2]) (ae_of_all _ fun i=> ((title A h ξ hp hz hc he x hx hQ x hx.le i).climb (he' i) le_rfl))
-- normalize numerator by base w mass at x. Tilt.Z getter.
variable (hq : 0< A.attends x)
local notation "h₀"=> (A.attends x)
include hq
lemma nominated : Brush j (q₀*M) 1 (fun y=>(h₀)⁻¹*heat A ξ y) x:= by
 have hx := (film A h ξ hp hz hc he x hx hQ hW hm).smul ((h₀)⁻¹); rw [Real.norm_of_nonneg (inv_nonneg.mpr hq.le), mul_left_comm,inv_mul_cancel₀ hq.ne',mul_one] at hx; exact hx
omit hW hQ hm
lemma crowned : Brush j q₀ 1 (fun y=> (h₀)⁻¹*A.attends y) x := by
 have ht:= (A.flora h hp hz hc _ hx he).smul ((h₀)⁻¹); rw [Real.norm_of_nonneg (inv_nonneg.mpr hq.le), mul_left_comm,inv_mul_cancel₀ hq.ne',mul_one] at ht; exact ht
end Gross
end YM.QuadraticLocal.Aperture
