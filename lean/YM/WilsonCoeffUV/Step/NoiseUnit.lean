import YM.WilsonCoeffUV.Step.Branches
import YM.Push.LOOP_COEFFICIENT.Tangent
import YM.LocalH.Haar
/-!
# One-link denominator of the normalized Markov kernel

Leading constants and powers *discarded* separately at each step (don't use
`zeta` as an estimator of the Gibbs vacuum factor!). Haar J is a choice of
actual LocalRatio, can take the physical Ñ. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV
open Wilson Lattice Laurent Exterior Bloch Matrix Precision Stationary RG Blue
open Next.Free FreeResolvent Tree Filter Gauge Metric Function
open PowerSeries
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge}

section jet
variable {X:Type*}[Fintype X]
-- exponential of ordinary analytic jet and determinant etc.
lemma literal_exp {f:Lawn X→ℝ}(h:Green f)(z:f 0=0): jet (fun i=> Real.exp (f i))=raiseE (jet f) := by
  have he: constantCoeff (jet f)=0:=by rw [jet_lead f,z,map_zero]
  let Q i:=Real.exp (f i)
  have hu : Green Q:= h.exp
  ext1 n; induction n using Nat.strong_induction_on with
  | h n ih=>
    apply pext (seed_eq (by
      rw [seed_jet, raise_map (φ:=seedH) _ he, seed_jet,fact (f:=f) z]
      · simp [z]
      simp [seedH]) n)
    intro x
    have H : rub Q x =ᶠ[𝓝 0] (Q*rub f x) := by
      filter_upwards [h.eventually (by simp)] with i hi
      unfold rub; rw [show fderiv ℝ Q i=_ from (((hi.differentiableAt (by simp)).hasFDerivAt).exp).fderiv];
      change Real.exp (f i)*_= Real.exp (f i)* _; rfl
    have ht: brush x (jet Q)= PowerSeries.X * (jet Q*jet (rub f x)) := by rw [sap hu,jet_congr H,jet_mul hu (rubbed h x)]
    rw [←blot_apply,←blot_apply]; change coeff _ (brush x (jet Q))= coeff _ (brush x _); rw [ht,show brush x _=_ from raise_diff he (MvPolynomial.pderiv x), show blot _ _= _ from sap h x,mul_left_comm (raiseE _)]
    cases n with
    | zero=> rw [coeff_zero_X_mul,coeff_zero_X_mul]
    | succ n=> rw [coeff_succ_X_mul,coeff_succ_X_mul]; exact ((show Equal _ (jet Q) _ from ih).mul (Equal.refl _ _)) n n.lt_succ_self
where
 fact {f:Lawn X→ℝ}(z:f 0=0): raiseE (PowerSeries.C (f 0))=1 := by
    rw [z,map_zero]; exact raise_unique _ (raise_change (by simp)) (by simp) (by rw [raise_one (by simp),map_one])
lemma literal_log {f:Lawn X→ℝ}(h:Green f)(z:f 0=1) : jet (fun x=>Real.log (f x))= logOf (jet f) := by
  let Q i:=Real.log (f i)
  have hz : Q 0=0 := by simp [Q,z]
  have hp : Green Q:= h.log (by rw [z]; norm_num)
  have he : constantCoeff (jet f)=1 := by rw [jet_lead,z,map_one]
  change jet Q=_; apply raise_inj (by rw [jet_lead,hz,map_zero]) (constantCoeff_logOf he)
  rw [raising_log he,← literal_exp hp hz];
  apply jet_congr; filter_upwards [h.continuousAt.eventually (lt_mem_nhds (show 0<f 0 by rw [z]; norm_num))] with x hx; exact Real.exp_log hx
end jet

section zeta
variable (Ñ:ChartRatio G)(κ:ℝ)
def coatC (G:Gauge) : Lawn G.ColorIndex ≃L[ℝ] G.Color := (WithLp.linearEquiv 2 ℝ (G.ColorIndex→ℝ)).symm.toContinuousLinearEquiv

def dij (x:Lawn G.ColorIndex):= Ñ.J (coatC G x)
def weightC (G:Gauge) (κ:ℝ) (x:Lawn G.ColorIndex) : ℝ:= κ * G.price (G.lieExp (coatC G x))
def towel (G : Gauge) (κ:ℝ) : Matrix G.ColorIndex G.ColorIndex ℝ:= κ • 1

def seedPay (x:Lawn G.ColorIndex) := weightC G κ x
lemma seedPay_green : Green (weightC G κ) := by
  apply ContDiffAt.mul contDiffAt_const
  apply Work.F03.price_smooth (A:=fun x=>G.lieExp (coatC G x)); exact (G.exp_jet.comp (coatC G).contDiff).contDiffAt
lemma seed_jets : weightC G κ 0=0 ∧ fderiv ℝ (weightC G κ) 0=0 ∧ ∀ x y, iteratedFDeriv ℝ 2 (weightC G κ) 0 ![x,y] = dotProduct x (towel G κ*ᵥ y) := by
  apply Work.F03.hessian_of_limit ((seedPay_green κ).of_le (by simp))
  · intro x; let v:=coatC G x
    have he := Work.F03.price_limit (V:=fun t:ℝ=> G.lieExp (t • v)) (by simp)
      (Push.side _ (G.expDiff_zero.differentiableAt) v |>.congr_deriv (DFunLike.congr_fun G.expDiff_zero.fderiv v))
    have hx : ‖v‖^2=dotProduct x x:= by rw [←real_inner_self_eq_norm_sq]; exact color_dot (G:=G) v v |>.symm
    simp_rw [towel,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul,weightC,map_smul, mul_div_assoc]
    rw [hx] at he; rw [smul_eq_mul, mul_div_assoc]; exact he.const_mul κ
  · intro x y z; rw [add_dotProduct]
  intro x y; simp_rw [towel,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul,dotProduct_comm y x]
lemma precision_one {κ:ℝ}(h:0<κ) : towel G κ*(κ⁻¹ • (1:Matrix G.ColorIndex G.ColorIndex ℝ))=1 := by rw [towel, mul_smul_comm,Matrix.mul_one,smul_smul,inv_mul_cancel₀ h.ne',one_smul]

def gust (G:Gauge)(κ:ℝ) : Ink G.ColorIndex := flash (sprig (weightC G κ) 2)-orbC (towel G κ)
lemma gust_zero : constantCoeff (gust G κ)=0 := by
  rw [gust,map_sub,←PowerSeries.coeff_zero_eq_constantCoeff_apply,Blue.flash,PowerSeries.coeff_mk, sprouts_lead (seedPay_green κ) (seed_jets κ).2.2 (by simp [towel]),visible_shine,orbC]; simp
-- expansion of single Haar integral exp gaussian with bare Haar density J; drop g^dim, scale per axis, Gaussian constant, det.
def ζ (Ñ:ChartRatio G) (κ:ℝ) : PowerSeries ℝ:= seedH (blur (κ⁻¹ • (1:Matrix G.ColorIndex G.ColorIndex ℝ)) (jet (dij Ñ)*raiseE (-gust G κ)))
variable {Ñ}
lemma dij_green (h:LocalRatio Ñ): Green (dij Ñ) := (show ContDiffAt ℝ ω Ñ.J (coatC G 0) from by rw [map_zero]; exact h.germ _ (mem_ball_self h.patch)).comp (f:=coatC G) 0 (coatC G).contDiff.contDiffAt
lemma ζ_one (h :LocalRatio Ñ): constantCoeff (ζ Ñ κ)=1:= by
  rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply,ζ,seedH,PowerSeries.coeff_map,overlay_apply,PowerSeries.coeff_zero_eq_constantCoeff_apply,map_mul,jet_lead,dij,map_zero,h.anchored,map_one,raise_one (by rw [map_neg, gust_zero, neg_zero]),one_mul,glaze_one,map_one]

end zeta
section Haar
variable {n : Side}
def dyes (x: TreeVars G n) (e: Edge (Site n)): Lawn G.ColorIndex := (coatC G).symm ((cloth G n).symm x (e.1,coord e.2))
def unhaar (Ñ:ChartRatio G)(x:TreeVars G n) := ∑ e:Edge (Site n),Real.log (dij Ñ (dyes x e))
lemma dyes_green (e:Edge (Site n)): Green fun x:TreeVars G n=> dyes x e := (coatC G).symm.contDiff.contDiffAt.comp (f:=fun x:TreeVars G n=> (cloth G n).symm x (e.1,coord e.2)) 0 ((contDiffAt_apply ℝ G.Color (e.1,coord e.2) _).comp 0 (cloth G n).symm.contDiff.contDiffAt)
lemma dyes_zero (e:Edge (Site n)): dyes (0:TreeVars G n) e=0:=by simp [dyes]
lemma unhaar_zero {Ñ:ChartRatio G}(h:LocalRatio Ñ): unhaar Ñ (0: TreeVars G n)=0 := by simp_rw [unhaar,dyes_zero,dij,map_zero,h.anchored]; simp
lemma unhaar_green {Ñ:ChartRatio G}(h:LocalRatio Ñ): Green (unhaar (n:=n) Ñ) := by
  apply ContDiffAt.sum; intro i _; apply ContDiffAt.log; apply ContDiffAt.comp (g:=dij Ñ) (f:=fun x:TreeVars G n=>dyes x i) 0 _ (dyes_green i); rw [dyes_zero]; exact dij_green h
  rw [dyes_zero,dij,map_zero,h.anchored]; norm_num
end Haar
end YM.WilsonCoeffUV
