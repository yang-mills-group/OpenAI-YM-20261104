import YM.Integration.WilsonReceivedSourceCoefficientBound
import YM.Integration.WilsonMarkedAngularTestInvoice
import YM.Integration.WilsonOriginalLinkedAngularPage

/-! Mixed coupling and angular coefficients of the actual paid group word on a periodic link board. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalGroupInkDirections
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry Exterior Stationary AllOrder.Fire
open WilsonOriginalLinkedAngularPage
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n:Side} {V X:Type} [DecidableEq V] {o:Passport n V} {J:Census V}

def pack (G:Gauge) : (G.ColorIndex→ℝ) ≃L[ℝ] G.Color :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun:=WithLp.toLp 2
    invFun:=WithLp.ofLp
    map_add':=fun _ _=>rfl
    map_smul':=fun _ _=>rfl
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }

def weight (G:Gauge) : ℝ := ‖(pack G : (G.ColorIndex→ℝ)→L[ℝ]G.Color)‖

theorem axis (A:Link G n) (e:Edge (Site n)) :
    ‖collect G (arm G n 1 A) e‖ ≤ weight G*‖A‖ := by
  let v:G.ColorIndex→ℝ:=fun i=>A (e.1,coord e.2,i)
  have hv:‖v‖≤‖A‖:=by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg A)).mpr
    intro i
    exact norm_le_pi_norm A _
  exact (((pack G : (G.ColorIndex→ℝ)→L[ℝ]G.Color).le_opNorm v).trans
    (mul_le_mul_of_nonneg_left hv (norm_nonneg _)))

def jet (T:Row o J G X) (t:X) (j:ℕ) (A:Link G n) : ℂ :=
  T.paint t * (T.markReceipt j A : ℝ)

def band (T:Row o J G X) (j:ℕ) := j-T.lamp.e+T.lamp.r
def price (G:Gauge) (σ:ℝ) (d r:ℕ) : ℝ :=
  WilsonMarkedAngularTestInvoice.fee d r*(max 1 (2*(G.colorScale*(weight G*d))/σ))^d

theorem rank (T:Row o J G X) (j d:ℕ) (h:band T j≤d) : Rank (Link G n) d (T.markReceipt j) := by
  by_cases live:T.lamp.e≤j
  · have eq:T.markReceipt j=PertExtension.Series.Radial.jet (Helmet.frame T.atom T.center) (band T j):=by
      funext a;exact if_pos live
    rw [eq]
    exact (AllOrder.Haiku.Project.maturity _ _).up h
  · have eq:T.markReceipt j=fun _=>0:=by funext a;exact if_neg live
    rw [eq]
    exact Rank.nil d 0

theorem paid (T:Row o J G X) (t:X) {σ:ℝ} (hs:0<σ) (deposit:T.Budget) (growth:T.Graceful σ)
    (j d r:ℕ) (h:band T j≤d) (hr:r≤d) (x:Fin r→Site n×Loc G 1) :
    ‖coefficient r (jet T t j) x‖ ≤ T.salary*price G σ d r := by
  let ink:=T.paint t
  let c:=weight G*d
  let u:=2*(G.colorScale*c)/σ
  have c0:0≤c:=mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
  have u0:0≤u:=div_nonneg (mul_nonneg (by norm_num) (mul_nonneg G.colorScale_pos.le c0)) hs.le
  let H:Link G n→ℝ:=fun a=>‖ink‖*T.markReceipt j a
  have degree:Rank (Link G n) d H:=(rank T j d h).scal _
  have cost:0≤T.salary*(max 1 u)^d:=mul_nonneg T.sound.le (by positivity)
  have bound (a:Link G n) (hab:‖a‖≤(d:ℝ)): |H a|≤T.salary*(max 1 u)^d:=by
    have ax (e:Edge (Site n)): ‖collect G (arm G n 1 a) e‖≤c :=
      (axis a e).trans (mul_le_mul_of_nonneg_left hab (norm_nonneg _))
    have val:=WilsonReceivedSourceCoefficientBound.row T t a hs c0 ax deposit growth j
    change |‖ink‖*T.markReceipt j a|≤_
    rw [abs_mul,abs_of_nonneg (norm_nonneg _)]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs] at val
    exact val.trans (mul_le_mul_of_nonneg_left
      ((pow_le_pow_left₀ u0 (le_max_right 1 u) _).trans (pow_le_pow_right₀ (le_max_left 1 u) h)) T.sound.le)
  have tariff:=WilsonMarkedAngularTestInvoice.linear hr degree cost bound
  let arg:Fin r→Link G n:=fun i=>ray G (x i)
  have halo (i):‖arg i‖≤1:=by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : 0≤(1:ℝ))).mpr
    intro y
    change ‖if y=x i then (1:ℝ) else 0‖≤1
    split <;> norm_num
  have paidReal:=((iteratedFDeriv ℝ r H 0).le_opNorm arg).trans
    (mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun i _=>norm_nonneg _) (fun i _=>halo i)))
  let re:ℝ→L[ℝ]ℝ:=(ContinuousLinearMap.id ℝ ℝ).smulRight ‖ink‖
  let co:ℝ→L[ℝ]ℂ:=(ContinuousLinearMap.id ℝ ℝ).smulRight ink
  have smooth:= (WilsonMarkedAngularTestInvoice.regular (rank T j d h) r).contDiffAt (x:=0)
  have hre:H=re ∘ T.markReceipt j:=by funext a;change ‖ink‖*T.markReceipt j a=T.markReceipt j a*‖ink‖;ring
  have hco:jet T t j=co ∘ T.markReceipt j:=by
    funext a;change ink*_=(T.markReceipt j a:ℝ) • ink;rw [Complex.real_smul];ring
  have equal:‖coefficient r (jet T t j) x‖=‖iteratedFDeriv ℝ r H 0 arg‖:=by
    change ‖iteratedFDeriv ℝ r (jet T t j) 0 arg‖=_
    rw [hre,hco,re.iteratedFDeriv_comp_left smooth le_rfl,co.iteratedFDeriv_comp_left smooth le_rfl]
    change ‖(iteratedFDeriv ℝ r (T.markReceipt j) 0 arg) • ink‖=‖(iteratedFDeriv ℝ r (T.markReceipt j) 0 arg) • ‖ink‖‖
    rw [norm_smul,norm_smul,norm_norm]
  exact equal.le.trans ((paidReal.trans tariff).trans_eq (by unfold price;change _=T.salary*(_*(max 1 u)^d);ring))

end YM.Integration.WilsonOriginalGroupInkDirections
