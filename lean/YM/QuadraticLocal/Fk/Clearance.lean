import YM.QuadraticLocal.Fk.Dress
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
/-!
The exact full Gaussian averaging law used by both Desk and Fk, after `.placed` and `.pay`.
Not only covariance: rewrite ANY Bochner kernel of this test. determinant charge certified
on this finite-dimensional measure and policy, with Energy & scalar lines. Connect next to
polynomial derivatives on actual schedule. AdvanceReceipt at payload.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Fk.Dress
open Filter Function Finset Lattice Wilson RG Pressure RG.Supply Input Org Precision
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat Lapis
open AllOrder AllOrder.Floe AllOrder.Response Extra.Iteration Tree Blaze MeasureTheory
open Comparison.RG02 Comparison.RG02.Bulk Assembly Next.SectorChange
open Marker Extra.Trajectories Multi Push Push.Uniform Laplace Laplace.SigmaP
open PertExtension PertExtension.Series PertExtension.GaussianScore
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge} {f c:Side}{V:Type}[DecidableEq V] {J:Census V} {S:StepData c f}
local notation "X"=> Apex c G
variable (F : Forest S.ratio) (k:S.Choices) {p:Clip}{R:PathData G}{O:ChartRatio G}
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "E"=> Apex c G × Poll.Body (Precision.Key F G)
local notation "χ"=> ℝ× (Apex c G × Poll.Body (Precision.Key F G))
local notation "v"=> weld (Precision.Key F G)
local notation "w"=> tint G (Exterior.Body 1 c)
local notation "r"=> (Precision.Key F G → ℝ)
variable (M:Layout G)(A:Finset Age)
variable (h:Legal A M)
variable (C:Bulk.Kernel S p R O)
variable {a C₀ Λ:ℝ}{N:ℕ} (F' : (Bid.Dir G c) → AxisChart G F) (U : Push.Uniform.Before G a C₀ S.patch.J S.kernel (N+3)) (hT:U.Service F p R F')
variable (hG:Bid.Larger (G:=G) S)(hQ:R.Bounds p a C₀ Λ)
local notation "K"=> Laplace.startup F O k R p U hG hQ hT C.ratio
local notation "K0"=> augment F M A K h
set_option quotPrecheck false
local notation "Γ"=> Response.castle (K0).hard (K0).quiet (K0).pay.steer
local notation "C'"=> C.covariance F k
local notation "Cost"=> (Gaussian.coat (C'))
local notation "μ"=> (volume: Measure Y)
lemma square_bridge (y:Y): (Γ).P y y=Gaussian.force (C') y.ofLp:=by
   have he:= curvature_spine F k R p U hG hQ hT y
   unfold Laplace.curvature at he; rw [Laplace.jet_two_H] at he
   unfold gram at he; rw [map_zero,hT.critical.1] at he;
   -- complete-square, invert Counting Hessian.Basis aligned, phi logging.OUT.Power wick no determinant convention drift.
   rw [Gaussian.force, Kernel.covariance, Matrix.nonsing_inv_nonsing_inv _ (IsUnit.mk0 _ (C.hessian_pos F k).det_pos.ne')];
   exact mul_left_cancel₀ (show (2:ℝ)⁻¹≠ 0 from by norm_num) (by simpa only [one_div] using! he)
-- Lp convention.Measure preservation holds finite c ANY G.
def gaussSkin (κ:Type) [Fintype κ]: EuclideanSpace ℝ κ ≃ᵐ (κ→ℝ) := (MeasurableEquiv.toLp 2 (κ→ℝ)).symm
local notation "H"=> gaussSkin (Precision.Key F G)
-- Kernel property, exposes EXACT scale factor for unmask/mark integrals. P.d mantle no Fill.Aux.
lemma normal_geom {Z:Type*}[NormedAddCommGroup Z][NormedSpace ℝ Z] (f:r→Z):
   (∫ y:Y,(Γ).kern y • f y.ofLp ∂volume) = Cost • (∫ y:r,f y ∂Gaussian.cloud (C')):=by
   have hp:= Gaussian.under_cloud (C.positive F k) (fun y:r=> Real.exp (-(Gaussian.force (C') y)/2) • f y); let g y:= Real.exp (-(Gaussian.force (C') y)/2) • f y
   have hh : MeasurePreserving (H) volume volume:= PiLp.volume_preserving_ofLp (Precision.Key F G)
   have hq:= hh.integral_comp' g
   calc _ = _ := (show (∫ y:Y,(Γ).kern y • f y.ofLp)=(∫ y:Y,g ((H) y)) from (by refine integral_congr_ae (Eventually.of_forall fun y=>?_); dsimp only []; rw [PertExtension.GaussianScore.Law.kern, square_bridge]; rfl)) -- implicit args? same term
        _ = _ := hq
        _ = _ := hp.2.trans (by rw [(funext fun y:r=> show Real.exp (Gaussian.force (C') y/2) • g y=f y from (by unfold g; rw [smul_smul,neg_div,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul]))])
lemma hull : capital (Γ) μ=Cost:= by
   let hz:= normal_geom (Z:=ℝ) F k M A h C F' U hT hG hQ (fun _=>1); simp only [smul_eq_mul,mul_one, integral_const,probReal_univ] at hz; exact hz -- probReal syntax
lemma bill (g:r→ℝ): (Γ).average μ (g ∘ H)= ∫ y:r,g y ∂Gaussian.cloud C':= by
   unfold Law.average; rw [show (∫ x:Y,(Γ).kern x)=Cost from hull .., div_eq_mul_inv, mul_comm _ (Cost)⁻¹]
   have hp : (∫ x:Y,((g∘H)*(Γ).kern) x)=Cost* (∫ y:r,g y ∂Gaussian.cloud C'):=by
      rw [mul_comm (g∘H) (Γ).kern]; exact normal_geom F k M A h C F' U hT hG hQ g
   rw [hp,inv_mul_cancel_left₀ (Gaussian.coat_pos (C.positive F k)).ne']
end YM.QuadraticLocal.Fk.Dress
