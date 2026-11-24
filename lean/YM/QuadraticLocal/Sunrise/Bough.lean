import YM.QuadraticLocal.Sunrise.Loan
import YM.QuadraticLocal.Sunrise.Attic
/-!
# Spurion leg book
 Concrete analytic family, all positions (later assign lav from projection before
 reading true local tests). No requirement smooth within position. Loan prices for rank-period
 kernels after. Extraction book equals PS shift at full Fk step with genuine vacuum/tape and
 condition weight. Arbitrary distinguished query at all regulators; binding to complete ANY 
 projective direction and same true input model. Polynomials linear at input, multiply on heat.
 Append ONE spurion leg per input atom; after propagation read at independent test/anchors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Sunrise
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open ConnectedActivityE6 Blaze
open AbsoluteSums Org
open Comparison.RG02 AllOrder AllOrder.Floe AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire PertExtension.Series Radial
open PertExtension AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method Laurent
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Comparison.RG02 Assembly Bulk Multi Marker
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge} {c f n : Side} {k j τ N : ℕ} {S:StepData c f}
variable {ι:Type}[Fintype ι] {V:Type}[Fintype V][DecidableEq V](J:Census V)
variable {σ C Z D β Θ:ℝ}
namespace Bough
variable (I:ι→ Loan)(u:∀i:ι,Atom G (I i).r)(α:∀ i:ι,Site c→ Site f) (L:Layout G)(T:Finset Age) (σ:rule ι c)
local notation "A₀"=> Apex c G
local notation "X"=> Apex c G × rule ι c
variable (F:Forest S.ratio)
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "P"=> rule ι c
local notation "E"=> (Apex c G × rule ι c) × (Poll.Body (Precision.Key F G))
local notation "χ"=> (Apex c G × Poll.Body (Precision.Key F G))
variable {o:ChartRatio G}{R:PathData G}{p:Clip}{t:S.Choices} {B:ℝ→ Config G f→ℝ} (W:Desk F o B t)
set_option quotPrecheck false
local notation "ϕ" i=> (I i).power
local notation "δ" i=> (I i).stamp
local notation "Ω" i:max x:max d:max=> (Loan.alloy (I i) (u i) (α i x) F d)
local notation "η"=> goldL F (fderiv ℝ W.quiet 0)
local notation "Ξ"=> books F L T W
local notation "K₀"=> castle W.hard W.quiet W.pay.steer
local notation "Π₀"=> ((ContinuousLinearMap.fst ℝ (Apex c G) (rule ι c)∘L ContinuousLinearMap.fst ℝ _ (Poll.Body (Precision.Key F G))).prod (ContinuousLinearMap.snd ℝ (Apex c G × rule ι c) _)) -- X path.M binder explicit.
-- definition censor using interest not depending local position incl global marks. no assumption α injective (fine sites allocation not tied yet).
def spect (j:ℕ)(x:E): ℝ:= Ξ j (x.1.1,x.2)
def soldier (i:ι)(x:Site c)(j:ℕ)(y:E) : ℝ:= y.1.2 (x,i)* ((Ω i x j) (η (y.1.1,y.2)))
def train (j:ℕ) := spect (ι:=ι) L T F W j + ∑ i:ι,∑ x:Site c,soldier I u α F W i x j -- binder order Universe from above
local notation "Φ"=> train I u α L T F W
variable (he:Legal T L)
lemma bye : Φ 0=0:=by
 unfold train soldier spect; ext1 v; simp_rw [Pi.add_apply,Finset.sum_apply,show books F L T W 0=0 from win0 _,Loan.gone]; simp
lemma full (j:ℕ) : Rank ((Apex c G × rule ι c) × Poll.Body (Precision.Key F G)) (j+2) (Φ j):= by
 refine ((show Rank E (j+2) (spect L T F W j) from (impulse_rank ..).lead (Π₀)).add (Rank.sum (fun i _=> Rank.sum fun x _=>?_))); let z:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Leaf c ι=>ℝ) (x,i) ∘L (ContinuousLinearMap.snd ℝ (Apex c G) (rule ι c) ∘L ContinuousLinearMap.fst ℝ X Y);
 exact Rank.dot z (j+1) ((Loan.outline (I i) (u i) (α i x) F j).lead ((η)∘L Π₀))
lemma evident : Clear Φ:= fun i=>(full I u α L T F W i).read
-- rooting all i ζ via self-direction projection; moment route unaffected
variable (z:Apex c G) (p':Book ((Apex c G × rule ι c) × (Poll.Body (Precision.Key F G))))
local notation "ϑ"=> ι → ℝ
def survey (x:ι→ℝ): rule ι c:=fun i=> σ i*x i.2
def surveyL : (ι→ℝ) →L[ℝ] rule ι c:= ContinuousLinearMap.pi (fun i=> σ i • (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _=>ℝ) i.2))
lemma translated : survey σ=surveyL σ:=rfl
def orient (j:ℕ)(x:(ι→ℝ) × Poll.Body (Precision.Key F G)):= p' j ((z,survey σ x.1),x.2)
local notation "η₀"=> orient σ F z p'
lemma guard (hx:Clear p'): Clear (orient σ F z p'):= by
 intro j; let X':=(ι→ℝ)× Poll.Body (Precision.Key F G); let A:X'→L[ℝ] Apex c G:=0;
 let C: X'→ Lattice.Site c → ℝ:= fun _=>0; let R':X'→L[ℝ]rule ι c:= surveyL σ ∘L ContinuousLinearMap.fst ℝ (ι→ℝ) _; let u₀:= (A.prod R').prod (ContinuousLinearMap.snd ℝ (ι→ℝ) _); let y:= ((z, (0:rule ι c)),(0:Poll.Body (Precision.Key F G))); have hV (x:X'): y+u₀ x=((z,survey σ x.1),x.2):= by
     exact Prod.ext (Prod.ext (add_zero _) (zero_add (survey σ x.1))) (zero_add x.2)
 let h: Plausible (fun x=> p' j (y + u₀ x)):= nearStep (B:=u₀.toLinearMap) y (hx j); unfold orient; simp_rw [hV] at h; exact h
lemma guard_vs (k:ℕ)(x:ϑ) : Response.connected (K₀) volume (η₀) k x= Response.connected (K₀) volume p' k (z,survey σ x):= by rfl
end Bough
end YM.QuadraticLocal.Sunrise
