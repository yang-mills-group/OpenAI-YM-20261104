import YM.QuadraticLocal.Sunrise.Bough
/-!
# Leg-wise Fk colors before surveying true test frame
Authenticates analytic marks THIS period, across all modes. Spurion arithmetic pressure on all
letters at ONCE. `RenderM` receives basis after survey routing around root(s) and projection,
 so *no* requirement covariance matrices at q>0.All analytic REAL fields in coordinates even
for imaginary/generator drivers after as pure cost probes. Full paints.ua.J.
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
variable {C Z D β Θ:ℝ}
namespace Balcony
open Bough
variable (I:ι→ Loan)(u:∀i:ι,Atom G (I i).r)(α:ι→Site c→ Site f) (L:Layout G)(T:Finset Age) (σ:rule ι c)
local notation "A₀"=> Apex c G
local notation "X"=> Apex c G × rule ι c
variable (F:Forest S.ratio)
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "P"=> rule ι c
local notation "E"=> (Apex c G × rule ι c) × (Poll.Body (Precision.Key F G))
local notation "χ"=> (Apex c G × Poll.Body (Precision.Key F G))
variable {o:ChartRatio G}{R:PathData G}{p:Clip}{t:S.Choices} {B:ℝ→ Config G f→ℝ} (W:AllOrder.Laplace.Desk F o B t)
set_option quotPrecheck false
local notation "ϕ" i:max=> (I i).power
local notation "δ" i=> (I i).stamp
local notation "Ω" i:max x:max d:max=> (Loan.alloy (I i) (u i) (α i x) F d)
local notation "η"=> goldL F (fderiv ℝ W.quiet 0)
local notation "Ξ"=> books F L T W
local notation "K₀"=> castle W.hard W.quiet W.pay.steer
local notation "Φ"=> train I u α L T F W
variable (he:Legal T L)
variable (z:Apex c G) (p':Book ((Apex c G × rule ι c) × (Poll.Body (Precision.Key F G))))
local notation "ϑ"=> ι → ℝ
local notation "η₀"=> Bough.orient σ F z p'
variable (w:V→ℕ)(Y':ι→ Hot J)(q:ι→ℂ)
def pigment (i:ι)(x:Site c)(s:ℝ) : Config G f →ℂ:= fun y=> (Complex.ofReal ((σ (x,i))*(Loan.letter (I i) (u i) (α i x) s y))) * q i
abbrev toneC (i:ι)(x:Site c) : ℝ→L[ℝ]ℂ := ((Complex.ofReal (σ (x,i))) * q i) • Complex.ofRealCLM
def feedM : Colors J G f:= { vac:=0, mark r s:=∑ i∈(Finset.univ.filter (fun i:ι=> r.val= (Y' i).val)),∑ x:Site c, pigment I u α σ q i x s, power r:=Launch.index J w r.val+1 }
abbrev feed : Colors J G f:= Fk.grant L T (feedM J I u α σ w Y' q)
local notation "τ₀"=> Balcony.feed J I u α L T σ w Y' q
local notation "pt" i:max x:max=> (pigment I u α σ q i x)
local notation "F₀"=> markFn S F τ₀
local notation "T'" i:max x:max=> (toneC σ q i x)
local notation "Fb" r:max=> (Finset.univ.filter (fun i:ι=> Subtype.val r=(Y' i).val))
lemma pig (i:ι)(x:Site c)(s:ℝ)(v:Config G f): (pt i x) s v= toneC σ q i x (Loan.letter (I i) (u i) (α i x) s v):= by unfold pigment toneC; simp only [ContinuousLinearMap.smul_apply,Complex.ofReal_mul,Complex.ofRealCLM_apply]; rw [smul_eq_mul]; ring
lemma griff (i:ι)(x:Site c): Bulk.projected (pt i x)=(T' i x) ∘ Bulk.projected (Loan.letter (I i) (u i) (α i x)):= funext fun z=> pig I u α σ q i x z.1 _
variable (hI:∀ i:ι,(I i).toll= Launch.index J w (Y' i).val)
omit [Fintype V]
include he hI
lemma standardF (hf:∀ i,(u i).Invariant) : Colors.Standard τ₀:= by
 apply Fk.standard L T he; -- `hf :...`
 · intro i; unfold feedM Bulk.projected; simp_rw [Finset.sum_apply]; apply GradeAt.list_sum; intro j hj; apply GradeAt.list_sum; intro x _; change GradeAt (Launch.index J w _+1) (Bulk.projected (pt j x)); rw [griff,(Finset.mem_filter.mp hj).2]; simp_rw [← hI j]; exact ((Loan.frame (I j) (u j) (α j x)|>.lower (Nat.le_add_right _ _)).linear_contact (T' j x))
 · intro i s g U; unfold feedM; simp_rw [Finset.sum_apply]; refine Finset.sum_congr rfl (fun j _=> Finset.sum_congr rfl fun x _=>?_); rw [pig,pig]; exact congr_arg ((T' j x)) ((Loan.natural (I j) (u j) (α j x) s (hf j)) g U)
 intro i s; let v:= (feedM J I u α σ w Y' q).mark i s; have hh: Continuous v:= by
    change Continuous (fun x=> v x); unfold v feedM; simp_rw [Finset.sum_apply]; apply continuous_finsetSum; intro j _; apply continuous_finsetSum; intro x _; change Continuous (fun y=> (pt j x) s y); simp_rw [pig]; exact Continuous.comp (g:=(T' j x)) (f:=Loan.letter (I j) (u j) _ s) ((toneC σ q j x).continuous) (Loan.conti ..)
 obtain ⟨K,hK⟩:= isCompact_univ.exists_bound_of_continuousOn hh.continuousOn; exact ⟨hh.measurable,K,fun i=> hK i (Set.mem_univ _)⟩
-- Bulk.projected tariff on couples. binding of Root direction after posting W choices.
omit he hI
local notation "E₁"=> Bulk.Joint (G:=G) S F
local notation "ϰ"=> QuadraticLocal.Fk.Dress.trim G F
-- only positive modes.
lemma censusF (i:Hot J) : F₀ i= ∑ j∈ Fb i,∑ x:Site c,(T' j x) ∘ (posed S F (Loan.letter (I j) (u j) (α j x))) := by ext1 v; unfold markFn posed feed Fk.grant feedM; simp_rw [Finset.sum_apply]; refine Finset.sum_congr rfl (fun j _=>Finset.sum_congr rfl fun x _=> pig I u α σ q j x v.1 _)
private lemma rowsF {XX YY:Type*}[NormedAddCommGroup XX][NormedSpace ℝ XX][NormedAddCommGroup YY][NormedSpace ℝ YY]{K':Type*}(J:Finset K')(f:K'→XX→YY)(he:∀ i∈J, ContDiffAt ℝ ω (f i) 0)(k:ℕ)(x:XX): Assembly.jet (∑ i∈J,f i) k x = ∑ i∈J,Assembly.jet (f i) k x:=by
 rw [Assembly.jet,iteratedFDeriv_sum_apply (fun i hi=> (he i hi|>.of_le le_top)),_root_.sum_apply, Finset.smul_sum]
lemma keepM (i:Hot J)(d:ℕ)(x:χ) : Assembly.jet (F₀ i) (d+1) (ϰ (1,x))= ∑ j∈ Fb i,∑ y:Site c,(T' j y) ((Ω j y d) x):=by
 let Ψ (j:ι)(y:Site c):= (posed S F (Loan.letter (I j) (u j) (α j y))); let ψ (j:ι)(y:Site c):= T' j y ∘ Ψ j y; have hc j y:ContDiffAt ℝ ω (Ψ j y) 0:= (joint_receipt S F (Loan.frame ..)).smooth; have hh j y:ContDiffAt ℝ ω (ψ j y) 0:= (toneC σ q j y).contDiff.contDiffAt.comp (f:=Ψ j y) _ (hc j y) -- Prop
 rw [censusF,rowsF]; swap;
 · intro i _; have he : ContDiffAt ℝ ω (∑ y:Site c,ψ i y) 0 := by rw [show (∑ y:Site c,ψ i y)=(fun x=> ∑ y:Site c, ψ i y x) from funext (fun _=> Finset.sum_apply ..)]; exact ContDiffAt.sum fun k _=> hh i k;
   exact he
 refine Finset.sum_congr rfl fun j _=> ?_ ; change Assembly.jet (∑ k:Site c,ψ j k) (d+1) (ϰ _) = _; rw [rowsF _ _ fun i _ => hh j i]; apply Finset.sum_congr rfl; intro k _; unfold ψ; rw [Loan.alloyJ]; exact (jet_apply_left (T' j k) (Ψ j k) (d+1) ((hc j k).of_le le_top) _).symm; -- replace yelling
end Balcony
end YM.QuadraticLocal.Sunrise
