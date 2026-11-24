import YM.FVA2.TaylorWick
import YM.XSpace.Bare
import YM.XSpace.VertexProducts
import YM.PertExtension.BareChart
import YM.PertExtension.PTBills

/-!
# XSpace's orbit tree diagram rule in Radial conventions

Reconcile the two chart Haar conventions, and verify that XSpace's polynomial Wick rule (all
orders, actual links, inverses in the power series algebra) agrees with the Radial stationary
expansion of *its* tree, as needed for identification of the independent regulated
coefficients with `Orb.diag`. We permit ∞ in the observable assumption for later use with smooth
windows.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.TreeFormal
open MeasureTheory Function Set Filter Module PowerSeries
open PertExtension PertExtension.GaussianScore PertExtension.Series PertExtension.Series.Radial XSpace
open Precision
open scoped Topology ContDiff BigOperators InnerProductSpace Classical ENNReal
variable {G:Gauge}{R:XSpace.Period}(T:R.Tree)
local notation "Φ"=> T.Field G
local notation "q"=> (T.action (G:=G))
local notation "γ"=> (T.quadratic G)

lemma action_radial (v:Φ): jet q 2 v= γ v v / 2:=by
    rw [jet,show (fun _ : Fin 2=> v) = ![v,v] from ?_,(T.action_jets G).2.2]
    · simp only [Nat.factorial_two,Nat.cast_ofNat]; ring
    funext i; fin_cases i <;> rfl

lemma coercive : ∃ c>0,∀ v:Φ, c*‖v‖^2≤ γ v v/2:=by
  obtain ⟨c,hc,H⟩:= quadratic_min q (fun v hv=>by rw [action_radial]; exact half_pos (T.quadratic_pos hv))
  refine ⟨c,hc,fun v=>?_⟩; rw [←action_radial T]; exact H v

def law (G:Gauge) : Law (T.Field G) where
  P:= T.quadratic G
  turns:= T.symmetric
  slope:= coercive T
  smooth:= by
    have he: (fun x:T.Field G=> T.quadratic G x x)=fun x=>2*jet (T.action (G:=G)) 2 x:= funext fun x=>by rw [action_radial]; ring
    rw [he]; exact continuous_const.mul (Radial.Smooth.continuousJet ..)

lemma same_kernel (v:Φ): kernel q v=(law T G).kern v:=by rw [kernel,action_radial,Law.kern]; ring_nf; rfl
lemma same_pair : Wick.color (law T G) (T.basis G).coord=Bare.Q T G:=by
  apply Next.Rank.Normal.Symmetric.ext; funext i j; change (( (law T G).wick _ _:ℝ):ℂ)=↑(_ : ℝ); rw [Wick.basis_cov]; rfl

def enter (f:Φ→ℝ): Bare.Series T G:= Taylor.expandTaylor (T.basis G) (Complex.ofRealCLM ∘ f)
lemma receipt (f:Φ→ℝ)(hf:ContDiffAt ℝ ∞ f 0): TaylorWick.Reads (enter T f) (T.basis G).coord (jet f):=by
   intro i x; change Taylor.evalAt (T.basis G) x _= _
   unfold enter Taylor.expandTaylor; rw [coeff_mk,Taylor.divided_realEval (T.basis G) i f (hf.of_le (by norm_cast; simp))]; rfl

lemma advance_exp : Bare.interactionExp T G= TaylorWick.Advance (Bare.interaction T G):=by
  apply PowerSeries.ext; intro i; rw [Bare.exponential_formula,TaylorWick.Advance,coeff_mk]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [Algebra.smul_def,IsScalarTower.algebraMap_apply ℚ ℂ, one_div,map_inv₀,map_natCast]

lemma same_calculation (Z:Bare.Series T G): Bare.diagrams T G Z=TaylorWick.Num (Wick.color (law T G) (T.basis G).coord) (Bare.interaction T G) (Bare.haar T G * Z):=by
   rw [same_pair]; apply PowerSeries.ext; intro i
   rw [Bare.diagram_coeff,Bare.weight,advance_exp,TaylorWick.Num,coeff_mk,mul_comm (Bare.haar T G),mul_assoc]

-- include the chart constant for each cotree link
abbrev trayScale (G:Gauge) := (Bare.chart G).scale
def cH (G:Gauge):= trayScale G ^ Fintype.card T.Free
lemma cH_pos (G:Gauge):0 < cH T G:= pow_pos (Bare.chart_ratio G).scale _

local notation "jx"=> (Chart.jacobian (U:=T.Free) (Bare.chart G))
lemma unmasked_haar: jx =ᶠ[𝓝 0] cH T G • (Bare.relative T):=by
   have hx (i:T.Free): ∀ᶠ x:T.Field G in 𝓝 0, Chart.fee (Bare.chart G) (x i)=trayScale G * (Bare.chart G).J (x i):=by
       let J:=(Bare.chart G).J
       have ht:Tendsto J (𝓝 0) (𝓝 1):= by
           have hv:= ((Bare.chart_ratio G).germ 0 (Metric.mem_ball_self (Bare.chart_ratio G).patch)).continuousAt.tendsto; rwa [(Bare.chart_ratio G).anchored] at hv
       have he:= (ht.comp (show Tendsto (fun x:Φ=>x i) (𝓝 0) (𝓝 0) from (continuous_apply i).tendsto (0:Φ))).eventually (lt_mem_nhds (show (0:ℝ)<1 from zero_lt_one))
       filter_upwards [he] with x hh; exact max_eq_left (mul_nonneg (Bare.chart_ratio G|>.scale.le) (le_of_lt hh))
   filter_upwards [Filter.eventually_all.mpr hx] with i hi
   change (∏ j, Chart.fee (Bare.chart G) (i j))= cH T G * Bare.relative T i
   simp_rw [hi]; rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]; rfl

lemma action_receipt : TaylorWick.Reads (Bare.interaction T G) (T.basis G).coord (layers q):=by
   intro i x; change Taylor.evalAt (T.basis G) x _= _; unfold layers
   by_cases h:i=0
   · subst i; rw [coeff_zero_eq_constantCoeff_apply, Bare.interaction_initial,map_zero]; simp
   rw [if_neg h,Bare.interaction_coeff T x h]; push_cast [jet]; rw [add_zero]

lemma full_receipt (b:Φ→ℝ)(hb:ContDiffAt ℝ ∞ b 0)(i:ℕ)(x:Φ):
    (jet (jx * b) i x:ℂ) = (↑(cH T G):ℂ) * Taylor.evalAt (T.basis G) x (coeff i (Bare.haar T G * enter T b)):=by
   let f:Φ→ℝ:=Bare.relative T
   have he : TaylorWick.Reads (Bare.haar T G * enter T b) (T.basis G).coord (jet (f*b)):= by
       have ht:TaylorWick.Reads (Bare.haar T G * enter T b) (T.basis G).coord (Zone.mul (jet f) (jet b)):= (receipt T f ((Bare.relative_smooth T G).of_le le_top)).prod (receipt T b hb)
       have hp (x:Φ): (fun i=>jet (f*b) i x)=Tested.conv (fun i=> jet f i x) (fun i=> jet b i x):=
          (Tested.directions (ContDiffAt.mul ((Bare.relative_smooth T G).of_le le_top) hb) x).unique ((Tested.directions (Bare.relative_smooth T G|>.of_le le_top) x).prod (Tested.directions hb x))
       intro j y; rw [ht j y,congr_fun (hp y) j]; simp [Tested.conv, Tested.term, Zone.mul, coeff_mul]
   have hv: (jx * b) =ᶠ[𝓝 0] cH T G • (f*b):= (unmasked_haar T (G:=G)).mono fun y hy=> by change jx y * b y= cH T G * (f y * b y); rw [hy]; exact mul_assoc ..
   have hy := (hv.iteratedFDeriv ℝ i).eq_of_nhds
   unfold jet; rw [hy, iteratedFDeriv_const_smul_apply (show ContDiffAt ℝ (↑i) (f*b) 0 from ((ContDiffAt.mul (Bare.relative_smooth T G|>.of_le le_top) hb)).of_le (by norm_cast; simp))];
   rw [_root_.smul_apply, smul_eq_mul]
   change _= (↑(cH T G):ℂ) * MvPolynomial.aeval (R:=ℂ) (fun j=> (((T.basis G).coord j x:ℝ):ℂ)) _; rw [he i x]; unfold jet; push_cast; ring

local notation "μ"=> Chart.tangent G T.Free

theorem normalized_radial (f:Φ→ℝ)(hf:ContDiffAt ℝ ∞ f 0):
    TaylorWick.into (PowerSeries.mk (Tested.divide (moment μ (jx*f) q) (moment μ jx q)))=
    Bare.normalized T G (enter T f):=by
   have hx (b:Bare.Series T G): Bare.normalized T G b=(Bare.diagrams T G 1)⁻¹*Bare.diagrams T G b:=rfl
   rw [hx,same_calculation,same_calculation,mul_one]
   refine TaylorWick.divided_wick _ _ (action_receipt T) (c:=cH T G) (cH_pos T G).ne' (?_) (full_receipt T f hf) (fun i x=>?_) (same_kernel T)
   · rw [coeff_zero_eq_constantCoeff_apply,Bare.haar_initial]
   have h:= full_receipt T (1:Φ→ℝ) contDiffAt_const i x; rw [mul_one,show enter T (1:Φ→ℝ)=1 from ?_,mul_one] at h; exact h
   unfold enter; change Taylor.expandTaylor (T.basis G) (fun _:Φ=> ((1:ℝ):ℂ))=1; rw [Taylor.expand_const,Complex.ofReal_one,map_one,map_one]
end YM.FVA2.TreeFormal
