import YM.MSbar.Duel.Metric
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Duel
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Further.GaussianScalar
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Tree
variable {G:Gauge}{c f:Side}{S:StepData c f}(F:Forest S.ratio) (R T:PathData G)(p q:Clip)(u:S.Choices) (ρ:fieldDir G c 1→AxisChart G F) (γ:ChartRatio G)
local notation "Π!"=>Primary c G
local notation "φ"=>Key F G
local notation "X"=> Joint F G
local notation "W"=> Positions (Primary c G)
local notation "J"=> Positions (Key F G)
local notation "L"=> Positions (Joint F G)
local notation "K"=> Push.Uniform.block (priced F u p R) 0
local notation "μ"=> PowerSeries.coeff
local notation "Y"=> center F ρ
local notation "i!"=> ink c q T
local notation "Δ"=>stampD F u G
local notation "I"=>hands F G
local notation "A"=>poring F ρ
local notation "C"=>straight F G
variable (h: S.patch.Branches S.kernel G)(hp: Premier (main f p R))(he: Critical F p R ρ)(ht:ClassicalMatch F p q R T ρ) (hx: Matrix.PosDef (Push.Uniform.block (priced F u p R) 0))
variable (B:Nesting G f) (v: Primary c G)(m:ℕ)(x: Positions (Joint F G))(hg:LocalRatio γ)
local notation "g"=> swung F γ
local notation "O"=> barbed F u γ B
local notation "f'"=> singularity (pushChart F G u) 2
local notation "F'"=> flux (I v)
lemma breeze (p: Positions (Joint F G)→ℝ)(he:ContDiffAt ℝ ω p 0) (hx:∀ i:Positions (Joint F G),∀ t:ℝ,p (i+t • hands F G v)=p i): dint (hands F G v) (potter p m)=0:=by
    let b:=I v; let f(x:L):= Tensor.diagonal (Tensor.coeff p m 0) x; apply MvPolynomial.funext; intro x; rw [← dimY]; simp_rw [pots]; rw [_root_.map_zero]
    have hz (x:L)(a:ℝ):f (x+a • b)=f x:=by
       unfold f Tensor.diagonal Tensor.coeff; simp only [_root_.smul_apply]; apply congr_arg; change Tensor.diagonal _ _=Tensor.diagonal _ x
       rw [← Next.Foundations.iteratedDeriv_on_line (he.of_le (m:=m) le_top) (x+a • b),← Next.Foundations.iteratedDeriv_on_line (he.of_le (m:=m) le_top) x]; apply congr_arg (fun k:ℝ→ℝ=> iteratedDeriv _ k _); exact funext fun t=>by rw [smul_add,smul_smul];exact hx ..
    have hs:HasDerivAt (fun t:ℝ=> f (x+t•b)) 0 0:=by simp_rw [hz]; exact hasDerivAt_const ..
    let t(y:ℝ):=x+y•b; have hT : HasDerivAt t b 0:=by simpa only [zero_smul,one_smul,zero_add] using (((hasDerivAt_id' (0:ℝ)).smul_const b).const_add x)
    have hq:= ((Tensor.diag_smooth (Tensor.coeff p m 0) ω).differentiable (by simp) (t 0)).hasFDerivAt.comp_hasDerivAt (0:ℝ) hT; rw [show t 0=x from (by unfold t; simp)] at hq; exact hq.unique hs
include hg
noncomputable def cycleP (F:Forest S.ratio)(u:S.Choices)(v:List (Primary c G)): SpringK (Joint F G) := batt (hands F G) (fun i=> flux (hands F G i) (-singularity (pushChart F G u) 2)) v
lemma canoe (hy:Kind B) : PowerSeries.C (stampD F u G v) + flux (hands F G v) (barbed F u γ B) = flux (hands F G v) (-singularity (pushChart F G u) 2):=by
   apply PowerSeries.ext; intro m; by_cases hv:m=0
   · subst m; rw [_root_.map_add,flux,ride,ride]; rw [show μ 0 (barbed F u γ B)=0 from ?_,_root_.map_zero,add_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_C]; unfold singularity; rw [_root_.map_neg,PowerSeries.coeff_mk, _root_.map_neg];rfl
     exact well F u γ B hy
   have hx : (pushG (G:=G) F) (hands F G v)=0:=(partSpace _ _|>.apply_symm_apply (bolt v,(0:J))) |> congr_arg Prod.snd
   rw [_root_.map_add,PowerSeries.coeff_C_of_ne_zero hv,zero_add]; unfold flux; rw [ride,barbed]; simp only [_root_.map_add,splitV,_root_.map_sub]; rw [PowerSeries.coeff_C_of_ne_zero hv, PowerSeries.coeff_C_of_ne_zero hv,PowerSeries.coeff_map,ride]; let D:= Rolling.rail (taps F G); let K':= dint (I v) (D (μ m B)); have hq : K'=0:=by
       unfold K'; rw [show dint _ (D _)= D _ from dimK _ _ _]; have ht:(taps F G)*ᵥ hands F G v=0:=by unfold taps; rw [LinearMap.toMatrix'_mulVec]; change stamp F G (pushG F _)= _; rw [hx,map_zero]
       rw [ht]; simp [dint]
   have hb : dint (hands F G v) (μ m (singularity (swung F γ) 0))=0:=by unfold singularity; rw [PowerSeries.coeff_mk]; refine breeze F v _ _ (swung_cont F γ hg) (fun i t=>?_); unfold swung;rw [map_add,map_smul,hx,smul_zero,add_zero]
   rw [hb, show dint (I v) _= (0:Pot (Joint F G)) from (show dint (I v) ((rail (taps F G)).toRingHom _) = 0 from hq)]; simp
lemma hand (hy:Kind B) : readScore (hands F G) (stampD F u G) (barbed F u γ B) = cycleP F u:=by unfold readScore cycleP; rw [show (fun i:_=>_)=_ from funext fun i:Primary c G=> canoe F u γ B i hg hy]
end YM.MSbar.Duel
