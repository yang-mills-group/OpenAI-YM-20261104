import YM.QuadraticLocal.Fk.Vesper
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Mural
/-!
# Exact perturbative Fk geometry in `Comparison/RG02/Bulk,Fk`
for analytic Vacuum + `D.mark` at every required order. Address ambiguity removed: use literally
same tree/t/step. No dropping Gaussian determinant normalization, etc. Knee.Hess at same response.
Both calculate one Gaussian with mean fderiv ℝ station. Even if `K.b F` (Critical Alg) has
no frozen extension enough for estimates, the formal input `_V` may present alternative chosen at
same germ via price Gap proof. Any `K` from `RunFormalChain` needs no additional identification.
(no UV compatibility here.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Fk.Dress
open Filter Function Finset Lattice Wilson RG Pressure RG.Supply Input Org Precision
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat Lapis
open AllOrder AllOrder.Floe Extra.Iteration Tree Blaze MeasureTheory
open Comparison.RG02 Comparison.RG02.Bulk Assembly Next.SectorChange
open Marker Extra.Trajectories Multi Push Push.Uniform Laplace Laplace.SigmaP
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge} {f c:Side}{V:Type}[DecidableEq V] {J:Census V} {S:StepData c f}
local notation "X"=> Apex c G
variable (F : Forest S.ratio) (k:S.Choices) {p:Clip}{R:PathData G}{O:ChartRatio G}
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "E"=> Apex c G × Poll.Body (Precision.Key F G)
local notation "χ"=> ℝ× (Apex c G × Poll.Body (Precision.Key F G))
local notation "L"=> (Lapis.combineH F)
local notation "w"=> weld (Precision.Key F G)
local notation "V"=> tint G (Exterior.Body 1 c) -- rename shadow V
local notation "Ω"=> Bulk.Joint (G:=G) S F
variable (M:Layout G)(A:Finset Age)
variable (h:Legal A M) (d:Colors J G f)
variable (C:Bulk.Kernel S p R O) (t:ℝ)
local notation "D'"=> tint G F.Free -- winding.K
-- Record binds every link for actual comparison, including sign & symmetry & n projection. paint values only unfold when exact.
def trim (G:Gauge){c f:Side}{S:StepData c f}(F:Forest S.ratio): (ℝ×(Apex c G × Poll.Body (Precision.Key F G)))≃L[ℝ] Bulk.Joint (G:=G) S F:=
   (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (Floe.slidL (G:=G) F)
local notation "Q"=> trim G F
set_option quotPrecheck false
local notation "B"=>Bulk.Joint (G:=G) S F
local notation "wD"=>QuadraticLocal.Fk.grant M A d
lemma orient (x:X) (y:Y) : trim G F (t,x,y)=(t,(V) x,(D') ((w) y)):= rfl
private lemma face (x:E) : (Lapis.table F k R p x)=Bulk.stone F k C (trim G F (0,x)):= by cases x; rfl
variable {a C₀ Λ:ℝ}{N:ℕ} (F' : (Bid.Dir G c) → AxisChart G F) (U : Push.Uniform.Before G a C₀ S.patch.J S.kernel (N+3))
    (hT:U.Service F p R F')
local notation "ρ"=> orbit F F'
local notation "Φ"=> fderiv ℝ (orbit F F') 0
include hT k
lemma purchase : F'=ᶠ[𝓝 0] C.b F := by obtain ⟨b,hb,hH⟩:=C.gap F; exact YM.PhysicalNext.Repeat.Pane.critical_single k hT.critical (C.critical F) hb hH
lemma Moved (x:X): fderiv ℝ (C.b F) 0 ((V) x)= (D') ((w) (Φ x)):=by
   let Rq:= ( (V).toContinuousLinearMap); let Qz:= ((D').toContinuousLinearMap ∘L (w).toContinuousLinearMap); let A':= (F'∘Rq);
   rw [← (purchase F k C F' U hT).fderiv_eq]; have hm: Continuous (Rq):= Rq.continuous
   let hz:= hT.critical; have hk: DifferentiableAt ℝ F' 0:= hz.2.1.differentiableAt (by simp)
   have ho : (Qz ∘ ρ)= A':= rfl; have hQ : DifferentiableAt ℝ (ρ) 0:= by
      -- orbit = inverse ∘ ...
      let q:= ((w).symm.toContinuousLinearMap) ∘L (D').symm.toContinuousLinearMap; rw [show ρ=q ∘ A' from rfl]; exact (q.differentiableAt).comp (f:=A') 0 (((Rq.map_zero).symm ▸ hk).comp _ Rq.differentiableAt)
   have hh : fderiv ℝ A' 0=fderiv ℝ F' 0 ∘L Rq:=by rw [fderiv_comp _ ((map_zero Rq).symm ▸ hk) Rq.differentiableAt,map_zero,ContinuousLinearMap.fderiv] -- A' def eq might rw
   have hx : fderiv ℝ (Qz ∘ orbit F F') 0 = Qz ∘L fderiv ℝ (orbit F F') 0:= by rw [fderiv_comp _ Qz.differentiableAt hQ, ContinuousLinearMap.fderiv]
   rw [ho] at hx; exact DFunLike.congr_fun (hh.symm.trans hx) x
lemma placed (x:X) (z:Y) : Q (Response.colorful (Φ) (x,z))= Bulk.translated C F (V x) z.ofLp:= by
   rw [Bulk.footing]; unfold Response.colorful; rw [orient, Moved F k C F' U hT]
   rw [map_add,map_add]; rfl
omit hT k
lemma priced (x:χ) : supplement S F (wD) (Q x)=venue F M A x:=by
   unfold supplement venue spark posed Fk.grant money;
   simp only [Finset.sum_apply]; rfl
lemma history : ((fun x:χ=> officer F C (Q x)))=ᶠ[𝓝 0] mist F O R ∘ Prod.snd:=by
   filter_upwards [( (continuous_snd.comp continuous_snd).continuousAt : ContinuousAt (fun x:χ=> x.2.2) 0).eventually (wind_gate F O C.ratio)] with x hx
   let t:= x.1; let p:=x.2.1; let y:=x.2.2; change officer F C ((Q) (t,p,y))=mist F O R (p,y)
   unfold officer; rw [orient,plume,Real.log_prod]; · rfl
   intro i _; have hy:= C.ratio.pos _ (hx i (Set.mem_univ _)); exact hy.ne' -- membership default
variable (hG:Bid.Larger (G:=G) S)(hQ:R.Bounds p a C₀ Λ)
local notation "K"=> Laplace.startup F O k R p U hG hQ hT C.ratio
local notation "K0"=> augment F M A K h -- actual
include hT k
lemma high_geom : (Bulk.geometric C F k wD ∘ (Q)) =ᶠ[𝓝 0] ((fun x=> (K0).high x+x.1^2* mist F O R x.2)):= by
   filter_upwards [Dress.history F C] with x hx; rcases x with ⟨t,u⟩; cases u with | mk x y=>
    unfold Function.comp Bulk.geometric Bulk.fee Bulk.pillar; rw [Dress.priced]; let A':= Lapis.table F k R p (x,y); change A' + ((t)^2*officer F C (Q (t,x,y))+ venue F M A (t,x,y))= (A'+venue F M A (t,x,y))+t^2*mist F O R (x,y); rw [hx]; dsimp only [Function.comp_apply]; ring
-- open Real
lemma pay_log : Real.log ∘ (K0).paid= (fun x=> (Fintype.card F.Free:ℝ)* Real.log O.scale - mist F O R x.2):=by
  ext1 x; unfold augment Laplace.startup; dsimp only [Function.comp_apply]; unfold Laplace.fixed;
  rw [Real.log_mul (pow_ne_zero _ (C.ratio.scale.ne')) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp]; ring
lemma minted : 0< (K0).paid 0:= mul_pos (pow_pos C.ratio.scale _) (Real.exp_pos _)
end YM.QuadraticLocal.Fk.Dress
