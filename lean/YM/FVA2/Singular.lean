import YM.FVA2.MirrorMeans
import YM.Contacts.Ion.Heme
/-!
# Exact account powers on the chosen frontier

 Show the bare primitives from paired stencils differ precisely by halving: squared
 coefficient series, i.e. half log. For already *interacting* U formed with conditional
 convolutions the corrections to the full-period seam would involve non-free loops; must
 not assert any such identification automatically.See `defectG` operation. Real branch
 evaluation no heuristics on angular multiplier at singular points. This is not estimating
 powered source period removal; that part of our solution for Main.Packed uses MS supplied
 momentum bounds **directly on the inversion regulator series** (before field normalization)
 rather than budget on the substantial lower mesh seam).
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2
open Function Filter Topology MeasureTheory Lattice Gauge RG _root_.YM.Wilson
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.BlockGauge
open PertExtension.Orb Precision GaussianScore RGComparison.Core16 RGComparison.Core16.Descent Tree Exterior Push.BetaTransport Tandem Luggage
open MeasureTheory.Measure (IsAddHaarMeasure)
open Contacts.Lyre Contacts.Lyre.Align Fabric CityHistory Mirror Blocking PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
section A
namespace Mirror.Trace
variable {E F:Type}[NormedAddCommGroup E][NormedAddCommGroup F][NormedSpace ℝ E][NormedSpace ℝ F][FiniteDimensional ℝ E][FiniteDimensional ℝ F]
variable (L:E→ₗ[ℝ] F)(V:E→ℝ)(W:F→ℝ)(h:W ∘ L=ᶠ[𝓝 0] V+V)
variable (he:ContDiffAt ℝ ω W 0)(ht:ContDiffAt ℝ ω V 0)
variable (w:PowerSeries ℝ)
-- no
lemma times (A B:E→ℝ)(hA:ContDiffAt ℝ ω A 0)(hB:ContDiffAt ℝ ω B 0): pay w (A+B)= pay w A+pay w B:= by
    unfold pay advancing; have he(k:ℕ)(F G:Ticket E): Stack.drop k (F+G)= Stack.drop k F+Stack.drop k G:= by apply PowerSeries.ext; intro i; unfold drop; rw [map_add,coeff_mk,coeff_mk,coeff_mk,map_add]
    rw [ ExactTower.up_add (hA.of_le le_top) (hB.of_le le_top),map_add,map_add, neg_add, he,he ]; ring
include ht h he
theorem squared (hp:Radial.Stationary V): boost L (chip w W)=chip w V*chip w V := by rw [ pullPay L _ _ he ]; unfold OpenSlots.chip; rw [← OpenSlots.compose_two _ _ ( OpenSlots.stipend _ _ hp ) ( OpenSlots.stipend _ _ hp ), ← times w V V ht ht ]; congr 1; unfold OpenSlots.pay advancing; rw [ExactTower.rise_local h]
end Mirror.Trace
end A
namespace Both
open Rent
variable {G: Gauge}{f c n:Side}(S:StepData c f)(h:S.patch.Branches S.kernel G)(he:Even f.val)(hc:Even c.val)(b:S.Choices)
local notation "T"=> Forestry S
local notation "P"=> canopy S
local notation "H"=> Both.orb G f he
local notation "K"=> Both.orb G c hc
local notation "Y"=> Both.lights G S he
local notation "Ψ"=> Mirror.House.join Y K
local notation "Q"=> Cross (G:=G) S P
local notation "M"=> Future G S T
local notation "L"=> Blocking.Index S P

-- Symmetric orientations. Build own equivalence with Contacts.Fore pros (including supporting Fintype proof). Haar path step.
def remapping : Blocking.Index S P≃ Rem S:= Equiv.subtypeEquivRight (by intro x; apply not_congr; exact branch_ident S _)
def bijpair : ( Blocking.Index S P ) × Bool ≃ ( Forestry S ).Free:= (Equiv.prodCongr (remapping S) (Equiv.refl Bool)).trans (Equiv.ofBijective (octave S) (Align.nocturne S he))
lemma rightPos (x:L) : bijpair S he (x,false)=rootFree S x:= rfl
lemma rightNeg (x:L) : bijpair S he (x,true)= Align.via S (rootFree S x):= rfl
variable (Z:ChartRatio G)(hz:LocalRatio Z)
local notation "𝕀"=> OpenSlots.tissue Z L
local notation "ν"=> OpenSlots.tissue Z ( Forestry S ).Free
include he hz
lemma jac_interpret : Chart.jacobian Z (U:=(Forestry S).Free) ∘ (Y).ε=ᶠ[𝓝 0] ( Chart.jacobian Z (U:=L) )^2:= by
    have hh(i:L): ∀ᶠ v:Q in 𝓝 0, v i∈ Metric.ball 0 Z.radius:= ((continuous_apply i).continuousAt (x:=(0:Cross (G:=G) S P))).eventually (Metric.ball_mem_nhds (0:G.Color) hz.patch);
    filter_upwards [ Filter.eventually_all.mpr hh ] with x hx; rw [ Pi.pow_apply, Function.comp_apply, jacobian, ← Equiv.prod_comp (bijpair S he), Fintype.prod_prod_type ]; unfold jacobian; rw [← Finset.prod_pow]; -- orientation
    apply Finset.prod_congr rfl; intro i _; rw [ Fintype.prod_bool, rightPos,rightNeg ]; have hv : (Y).ε x (rootFree S i)= x i:= congr_fun ((Y).recovery x) i; have ht: (Y).ε x (Align.via S (rootFree S i))= -((Y).ε x (rootFree S i)):= by
        obtain h:= congr_fun ((Y).assess x) (rootFree S i); change -_= _ at h; rw [ ←h,neg_neg ]; rfl
    rw [ ht,hv, ← Align.collected hz _ ( hx i ),pow_two ]

lemma print_path : boost (lights G S he).ε (OpenSlots.tissue Z ( Forestry S ).Free)= 𝕀*𝕀:= by
   obtain hJ:= jac_interpret S he Z hz; let f:= Chart.jacobian Z (U:=L); let F:= Chart.jacobian Z (U:=( Forestry S ).Free); let v:ℝ:= f 0; let L':=(lights G S he).ε; have he : F 0= v^2:= by obtain he:=hJ.self_of_nhds; rw [Pi.pow_apply, Function.comp_apply,map_zero] at he; exact he
   unfold tissue; rw [map_mul,FormalOPE.RG10.MarkovChain.Vault.climbing L' (( Chart.Ratio.jacobian_smooth hz|>.of_le le_top )),boost_c ]; -- he argument shadows he
   change roll ((F 0)⁻¹)*rise (F ∘ L')=(roll v⁻¹*rise f)*(roll v⁻¹*rise f); rw [ExactTower.rise_local hJ, ExactTower.rise_pow (f:=f) ((Chart.Ratio.jacobian_smooth hz|>.of_le le_top)), he ]; simp_rw [← inv_pow, roll,map_pow ]; ring

-- squared forms TRUE at initial and substeps, using label transformation.
variable (w: PowerSeries ℝ)
omit hz in
lemma bootPay : boost ( H ).ε ( chip w (bareF G f) )= ( initialFull G f w|>.W )^2:= by
    rw [pow_two]; refine Mirror.Trace.squared (H).ε firstBill (bareF G f) ?_ ( CityHistory.Legacy.born_hot .. ) OpenSlots.firstGranted w ?_; -- order ht
    · filter_upwards with v; rw [Pi.add_apply,← two_mul]; exact Rent.top_bridge v
    exact OpenSlots.first_held

include h hc in
lemma producer : boost ( Ψ ).ε ( chargeStep S T Z b w )= ( boost (LinearMap.fst ..) ( OpenSlots.tissue Z L ) * chip w ( substep P b ) )^2:= by
    let A:= OpenSlots.tissue Z L; let r:= LinearMap.fst ℝ ( Cross (G:=G) S P ) (Flats G c)
    have heq: boost (Ψ).ε (boost (LinearMap.fst ℝ (Future G S T) (Pins G c)) ν)= ( boost r A )^2:= by
        rw [show boost (Ψ).ε (boost (LinearMap.fst ..) ν) = boost r (boost ( Y ).ε ν) from (?_), Both.print_path S he Z hz,map_mul,pow_two ];
        apply Stack.into; intro x; simp_rw [caught]; rfl
    have hu: boost (Ψ).ε (chip w (tax S T b ( G:=G )))= chip w ( substep P b ) * chip w ( substep P b ):= by
        apply Mirror.Trace.squared _ _ _ ?_ (tax_hot S T b h) (OpenSlots.subReady P b h) _ ( OpenSlots.subStill P b h ); convert Rent.tollage S h he hc b using 1; ext1 v; change _+_=(2:ℝ)*_; rw [two_mul]
    unfold chargeStep; rw [ map_mul,heq, hu,mul_pow,pow_two (chip _ _) ]
end Both
end YM.FVA2
