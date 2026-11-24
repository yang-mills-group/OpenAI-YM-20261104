import YM.QuadraticLocal.Poetry.Vernal
import YM.Comparison.RG02.Symmetry.Code
import YM.AllOrder.Kinetic.Lily
/-!
# Convert exact Fk Mark polynomial real witnesses to Vernal.
 t may be one-sided; use along.IF probes all; birth arches.That port still needs loan.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Ker AllOrder.Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response AllOrder.Ink AllOrder.Ink.Method GaussianScore Module Push AllOrder.Ink.Money
open Marker Multi Comparison.RG02
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
open Comparison.RG02.Symmetry -- remove
open Symmetry.Orbit Kinetic.Port
variable {G:Gauge}{c:Side} {k:ℕ}
local notation "E"=> Stationary.Link G c
set_option quotPrecheck false
local notation "Θ" => ((exteriorL G c).trans (tint G (Exterior.Body 1 c)))
variable {F:Book (Stationary.Link G c)} {u: ℕ → Exterior.fieldDir G c 1 →ℂ}
variable (h: ∀ i≤k, u i ∘ ((exteriorL G c).trans (tint G (Exterior.Body 1 c)))= Complex.ofReal ∘ F i) (he : Sheet k u)
open Moving Moving.Path
local notation "σ"=> Comparison.RG02.Laplace.along
lemma rings (A:ℝ→ E)(t:ℝ): Haiku.life (G:=G) A t= Integral.sample t (Θ (A t)):= by unfold Haiku.life Integral.sample; rw [← map_smul Θ]; rfl
lemma alongC {a b:ℝ→ E}{x:ℝ→ Site c→ G.El}{s:G.El}(hz:Tendsto x (𝓝 0) (𝓝 fun _=>s))(hy:Haiku.life (G:=G) b=ᶠ[𝓝 0] fun t=> gauge (x t) (Haiku.life (G:=G) a t)):
    Comparison.RG02.Symmetry.Flow (⇑(Θ) ∘ b) (⇑(Θ) ∘ a):= ⟨s,x,hz.mono_left (show σ ≤ 𝓝 0 from nhdsWithin_le_nhds), Eventually.filter_mono (show σ ≤ 𝓝 0 from nhdsWithin_le_nhds) (by filter_upwards [hy] with y h; rw [Function.comp_apply,Function.comp_apply,← rings,← rings]; exact h)⟩
include h he
lemma read_path {j:ℕ}(hj:j≤k)(v:ℝ→ E)(hv:ContDiffAt ℝ ω v 0) : patrol j u (Θ ∘ v)=Complex.ofReal (weigh v F j):=by
 have hF (i)(hi:i≤k): ContDiff ℝ ω (F i):= by
    have hx:F i = Complex.reCLM ∘ u i ∘ Θ:= by rw [h i hi]; rfl; -- rfl.ofReal
    rw [hx]; exact Complex.reCLM.contDiff.comp ((he.known i hi).comp ((Θ).contDiff))
 unfold patrol weigh; rw [Complex.ofReal_sum,← Finset.sum_range_reflect]; -- choose reflection left.U; Nat order budget.he
 refine Finset.sum_congr rfl fun i hi=> ?_
 have hJ:= mem_range.mp hi; simp only [Nat.add_sub_cancel]; rw [show j-(j-i)=i by omega] -- may not there
 have h':ContDiffAt ℝ ω (F i ∘ v) 0:= (hF i (by omega)).contDiffAt.comp _ hv; rw [← comp_assoc,h i (by omega),comp_assoc]
 change Assembly.jet (Complex.ofRealCLM ∘ (F i ∘ v)) (j-i) 1=Complex.ofRealCLM _; rw [← Assembly.jet_apply_left Complex.ofRealCLM (F i ∘ v) (j-i) (h'.of_le le_top)]
 apply congr_arg Complex.ofRealCLM; symm; change PositionX.Jet.someJ (fun t=>F i (v t)) (j-i)= Radial.jet _ _ _; simpa only [Function.comp_def,smul_eq_mul,mul_one] using (jet_entry (h:=(F i ∘ v)) (n:=j-i) (h'.of_le le_top) (1:ℝ))
lemma stained {j:ℕ}(hj:j≤k): Haiku.Vernal G c F j:= by
 refine ⟨fun a b u' x ha hb hh hx=>?_⟩; apply Complex.ofReal_injective; rw [← read_path h he hj a ha,← read_path h he hj b hb]
 exact (he.follows _ _ (alongC hh hx) ((Θ).contDiff.contDiffAt.comp _ hb) ((Θ).contDiff.contDiffAt.comp _ ha) _ hj).symm
end YM.QuadraticLocal.Poetry
