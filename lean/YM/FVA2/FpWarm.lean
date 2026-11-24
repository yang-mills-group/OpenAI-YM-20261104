import YM.FVA2.PriceTower
import YM.FVA2.FpChartAll
import YM.FVA2.Landau
/-!
# Equality of formal expectations using any admissible based linear gauge with Gaussian gauge cost

Same log links/action/Haar as Orb/PhysicalSum. It is **not** the claim that other
distinct comparator packages have matched all taps. Delta transverse already in
OrbitConnection. Here really compare the additional smoothing gauge cost (every PD covariance).
Also positive_... and coordinate-independent `Law` gap and Wick prices in the `Rebase` section.
Works for the germs of physical insertions (much more than only ranks proj OP). The subsequent powers
of t/x used in physical normalization etc must be treated after these exact identities.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 250000
noncomputable section
namespace YM.FVA2
open MeasureTheory Filter Function PertExtension PertExtension.Chart PertExtension.Orb FormalOPE.RG10 FormalOPE.RG10.BlockGauge PowerSeries
open PertExtension.Series PertExtension.Series.Radial PertExtension.GaussianScore MeasureTheory.Measure
open Precision TreeBasis TreeBasis.SectionBasis GermLaplace GermLaplace.Rates MultiGauge
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
section H
namespace GermLaplace
variable {E F : Type}[NormedAddCommGroup E][NormedAddCommGroup F][NormedSpace ℝ E][NormedSpace ℝ F][FiniteDimensional ℝ E][FiniteDimensional ℝ F]
def sol (f:E→ℝ)(h:Gap f): Law E where
    P:= Splice.polar f
    turns x y:= by rw [Splice.side_p, Splice.side_p f y,add_comm]
    slope:= by simp_rw [Splice.origin_p]; exact h
    smooth:= by
        letI := borel E
        rw [show (fun x:E=> Splice.polar f x x)= (fun x=> 2*jet f 2 x) from funext (fun i=> by rw [← Splice.origin_p ]; ring)]; exact continuous_const.mul (Smooth.continuousJet ..)
omit [FiniteDimensional ℝ E] in
lemma Solvents (f:E→ℝ)(h:Gap f)(u:E): (sol f h).P u u / 2=jet f 2 u:= Splice.origin_p f u
lemma sol_k {f:E→ℝ}(h:Gap f): (sol f h).kern = kernel f:= by
   ext1 x; unfold Law.kern kernel; rw [← Solvents _ h, neg_div]
lemma uniquely_p (Λ Θ:Law E) (hp:∀ x, Λ.P x x = Θ.P x x): Λ=Θ:= by
   have he: Λ.P=Θ.P:= LinearMap.ext (fun x=> LinearMap.ext (fun y=> by
      have hz:=hp (x+y); simp_rw [map_add, LinearMap.add_apply, Λ.turns y x, Θ.turns y x,hp] at hz; linarith))
   cases Λ; cases Θ; congr
lemma sol_any (Λ:Law E){f:E→ℝ}(h:Gap f)(hp:∀ u, Λ.P u u/2= jet f 2 u): sol f h=Λ:= uniquely_p _ _ fun u=> by obtain hx:=Solvents f h u; rw [← hp] at hx; linarith [hx]
-- supply any chosen positive definite gauge cost on a finite-dimensional space
def pd (P:E→ₗ[ℝ] Module.Dual ℝ E)(h:∀ x y,P x y=P y x)(he:∀ x,x≠0→0<P x x): Law E where
     P:= P
     turns:=h
     slope:= by
         let p:=fun y=>P y y/2
         let L:= (((LinearMap.toContinuousLinearMap (E:=E) (F':=ℝ)).toLinearMap.comp P).toContinuousLinearMap)
         have hp: ContDiffAt ℝ ω p 0:= (L.contDiff.contDiffAt.clm_apply contDiffAt_id).div_const _
         have heq(x:E): jet p 2 x=p x:= by
             have hm(t:ℝ): p (t•x)=t^2*p x:= by unfold p; rw [map_smul,map_smul,LinearMap.smul_apply]; simp [smul_eq_mul]; ring
             rw [homogeneous_derivative p x 2 (hp.of_le le_top)]; simp_rw [hm,iteratedDeriv_mul_const_field,iteratedDeriv_fun_pow_zero]; norm_num [Nat.factorial]; ring
         obtain ⟨c,hc,h⟩:=Radial.quadratic_min p (fun x hx=> by rw [heq]; exact half_pos (he x hx))
         simp_rw [heq] at h; exact ⟨ c,hc,h⟩
     smooth := (((LinearMap.toContinuousLinearMap (E:=E) (F':=ℝ)).toLinearMap.comp P).toContinuousLinearMap.continuous.clm_apply continuous_id)
namespace Invoice
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[IsAddHaarMeasure μ]
def power (Λ:Law E)(f J:E→ℝ) : PowerSeries ℝ := Splice.input Λ μ (Stack.rise J * Stack.exponential (Stack.advancing f))
lemma price {f:E→ℝ}(h:Gap f)(J:E→ℝ): C (ExactTower.capital (sol f h) μ)* power μ (sol f h) f J = M μ J f:= ExactTower.ticketed _ _ _  (sol_k h).symm J -- syntax
lemma remains {f:E→ℝ}(h:Gap f){K:E→ℝ}(hK:constantCoeff (M μ K f) ≠ 0)(J:E→ℝ): ratioM μ K J f= power μ (sol f h) f J * (power μ (sol f h) f K)⁻¹:= by
    apply Rates.agree ?_ hK (price μ h J).symm (price μ h K).symm; rw [← price μ h K, map_mul] at hK; exact right_ne_zero_of_mul hK
end Invoice
end GermLaplace
end H
namespace Wilson
namespace FP
open Lattice Gauge Wilson
/-- Canonical Fintype Instance for the FP realization only (in scope SmoothGauge). The
 mathematical site space is identical to the computable version. Please use this convention if
 invoking the smoothed gauge chart. -/
abbrev population {V E : Type} [Fintype V] (D : Loom V E) : Fintype (Nonroot D) := inferInstance
namespace SmoothGauge
scoped instance (priority:=1500) (n:Side) : Fintype (Nonroot (rim n)):= population _
end SmoothGauge
open scoped YM.FVA2.Wilson.FP.SmoothGauge
variable {G:Gauge} {n:Side} (Z:GaugeSlice G n)(U:ChartRatio G)(H:LocalRatio U)(hn:_root_.Even n.val)
local notation "P" => Root (rim n) G
local notation "F" => Field G n
local notation "L" => Z.equiv.toContinuousLinearEquiv
local notation "K" => Z.anchor
local notation "μ" => tangent G (staple n).Bulk
local notation "ν" => tangent G (Nonroot (rim n))
local notation "σ" => Measure.prod ν μ -- Lean syntax?

variable {O:Wilson.Observable G n} (hp:Physical O)(he: Honest O)

abbrev θpay (O:Wilson.Observable G n): Cone G n→ℝ := O ∘ assemble G n
include hp
lemma finite_pay : θpay O =ᶠ[𝓝 0] treed O ∘ treeLog G (staple n) := by
   filter_upwards [fixed_eventual G (staple n)] with x hx; exact (hp _ ((staple n).frame_root _) _).symm.trans (congr_arg (fun u=> O (Orb.liftLinks u)) hx)
lemma charge_pay : θpay O ∘ L =ᶠ[𝓝 0] (treed O ∘ Prod.snd) ∘ K := by
   have ha:Tendsto L (𝓝 0) (𝓝 0):= by simpa using (L).continuous.tendsto 0
   exact (finite_pay hp).comp_tendsto ha
omit hp

variable (Γ:Law (Root (rim n) G))
-- addFree gauge fixing; gauge term is directly included in `f` with same covariance
-- and not an implicit assumption from closeness to actual massless diagrams.
def finances (A: Cone G n): ℝ:= pricing G n A + Rates.value Γ (Z.projection A)
def volumeK (O:Wilson.Observable G n)(A:Cone G n): ℝ := θpay O A * (density (OEdge n) U A * Z.AP A)
local notation "ΓFree" => addFree Γ (treeS G n)
def treeFacts (O:Wilson.Observable G n): F→ℝ := treed O * density (staple n).Bulk U

lemma financesL : finances Z Γ ∘ L=ᶠ[𝓝 0] (ΓFree) ∘ K:= (charge_pay Z (Physical.energy G n)).mono fun x h=> by
    change θpay _ _= treed (A:= _root_.YM.Wilson.energy) _ at h
    have hx : Z.projection ( (L) x)=x.1:= by change (Z.equiv.symm (Z.equiv x)).1=x.1; rw [LinearEquiv.symm_apply_apply]
    unfold Function.comp finances; rw [hx]; unfold pricing
    rw [ show _root_.YM.Wilson.energy (assemble G n ((L) x))= _ from h ]; exact add_comm ..
include H hp in
lemma paidL : volumeK Z U O ∘ L=ᶠ[𝓝 0] (fun x=> ((treeFacts U O) ∘ Prod.snd) ( (K) x ) * (fderiv ℝ K x).det):= by
    filter_upwards [Z.flash U H, charge_pay Z hp] with x hx h; change θpay O ((L) x)*(density (OEdge n) U ((L) x)* Z.AP ((L) x))= _; rw [show θpay O ((L) x)= _ from h, show density (OEdge n) U ((L) x)* Z.AP ((L) x) = _ from hx]; exact (mul_assoc ..).symm
-- local price lem
include hp he in
lemma finances_p : ContDiffAt ℝ ω (θpay O) 0:= ((ContDiffAt.comp (f:=treeLog G (staple n)) 0 (by rw [treeLog_zero]; exact he) (priceHot G (staple n)))).congr_of_eventuallyEq (finite_pay hp)
include he
include H in
lemma facts_hot : ContDiffAt ℝ ω (treeFacts U O) 0:= ContDiffAt.mul he (density_hot U H)
include H hp in
lemma vol_hot : ContDiffAt ℝ ω (volumeK Z U O) 0:= ContDiffAt.mul (finances_p hp he) ((density_hot U H).mul Z.Agg_hot)
omit he

lemma spendingL : ContDiffAt ℝ ω (finances Z Γ ∘ L) 0:= ((ContDiffAt.comp (f:=K) 0 (by rw [Z.anchored]; exact combined_hot _ (treeS_hot G n)) Z.anchor_hot)).congr_of_eventuallyEq (financesL Z Γ)
lemma action_direct : finances Z Γ= (finances Z Γ ∘ L) ∘ (L).symm:= by ext1 u; simp
lemma spending_hot : ContDiffAt ℝ ω (finances Z Γ) 0:= by rw [action_direct]; exact ContDiffAt.comp (f:=(L).symm) 0 (by rw [map_zero]; exact spendingL Z Γ) (L).symm.contDiff.contDiffAt
lemma spending_statL : Radial.Stationary (finances Z Γ ∘ L):= changed_stat (K) Z.anchor_hot Z.anchored (combined_stat Γ (aptitude G n)) (combined_hot Γ (treeS_hot ..)) (financesL Z Γ)
lemma spending_stat : Radial.Stationary (finances Z Γ):= by rw [action_direct]; exact rebase_stat (L).symm (spending_statL Z Γ)
include hn
lemma spending_gapL : Gap (finances Z Γ ∘ L):= by unfold Gap; rw [pulled_cost (K) Z.anchor_hot Z.anchored Z.anchor_one (combined_stat Γ (aptitude ..)) (combined_hot Γ (treeS_hot ..)) (financesL Z Γ)]; exact combined_gap Γ ((treeS_hot ..).of_le le_top) (quotient_gap G hn)
lemma spending_gap : Gap (finances Z Γ):= by rw [action_direct]; exact rebase_gap (L).symm ((spendingL Z Γ).of_le le_top) (spending_gapL Z hn Γ)
omit hn in
private lemma doubleH : IsAddHaarMeasure (Measure.prod (tangent G (Nonroot (rim n))) (tangent G (staple n).Bulk)) := by apply MeasureTheory.Measure.prod.instIsAddHaarMeasure
include H
include hp he in
theorem priced_all : M σ (volumeK Z U O ∘ L) (finances Z Γ ∘ L) = C (ExactTower.capital Γ ν)* sliceRows Z U O:= by
    haveI : IsAddHaarMeasure σ:= doubleH
    rw [ show sliceRows Z U O= M μ (treeFacts U O) (treeS G n) from congr_arg PowerSeries.mk (to_tree Z hn U H hp he).symm ]; refine Eq.trans ?_ (add_free_const μ ν Γ ((treeS_hot G n).of_le le_top) ((facts_hot U H he).of_le le_top)) -- g annotate
    exact congr_arg PowerSeries.mk (powerSeries_gauge σ K (anchor_hot Z) Z.anchored Z.anchor_one (combined_stat Γ (aptitude ..)) (combined_gap Γ ((treeS_hot ..).of_le le_top) (quotient_gap G hn)) (combined_hot Γ (treeS_hot ..)) ((facts_hot U H he).comp (f:=Prod.snd) 0 contDiffAt_snd) (ContDiffAt.comp (f:=L) 0 (by rw [map_zero]; exact vol_hot Z U H hp he) (L).contDiff.contDiffAt) (financesL Z Γ) (paidL Z U H hp)).symm

variable (V:Measure (Cone G n))[IsAddHaarMeasure V]
lemma earned_one : 0 < constantCoeff (M V (volumeK Z U 1) (finances Z Γ)):= by
    apply market V (spending_gap Z hn Γ) (spending_stat Z Γ) ((vol_hot Z U H (Physical.one G n) one_honest).of_le le_top); unfold volumeK θpay; rw [Agg_alive,density_zero U H]; simp
include hp he
/-- smooth linear based gauge (gauge term convolved). Exact formal Wilson power series
 incl Haar and arbitrary positive gauge width. Width parameter incorporated before Taylor,
 only one vacuum norm and same volume/dimension normalization. Finite-order arguments are
 consistent because these are equalities of entire series. -/
lemma all_basis : ratioM V (volumeK Z U 1) (volumeK Z U O) (finances Z Γ)= sliceEval Z U O:= by
    haveI : IsAddHaarMeasure σ:= doubleH
    have hz:= earned_one Z U H hn Γ V; have hb:= other_basis σ V L ((spending_hot Z Γ).of_le le_top) ((vol_hot Z U H hp he).of_le le_top) ((vol_hot Z U H (Physical.one G n) one_honest).of_le le_top) hz.ne'
    rw [←hb]; apply agree (one_core Z hn U H) ?_ (priced_all Z U H hn hp he Γ) (priced_all Z U H hn (Physical.one G n) one_honest Γ)
    rw [priced_all Z U H hn (Physical.one G n) one_honest Γ,map_mul]; exact mul_ne_zero ((PowerSeries.constantCoeff_C (ExactTower.capital Γ ν)) ▸ (Splice.positive ..).ne') (one_core Z hn U H)
theorem fp_order : PowerSeries.mk (Orb.diagonalWith U (Orb.restrictedO O))= ratioM V (volumeK Z U 1) (volumeK Z U O) (finances Z Γ) := (tree_identity Z hn U H hp he).trans (all_basis Z U H hn hp he Γ V|>.symm)

-- RG10 Laurent prefactors vs open Wick. Compute in any elected covariance basis,
-- including (commonly) Splice.fast ... if it realizes this finite Hessian.
lemma gaugeWick (Λ:Law (Cone G n))(h:∀ A, Λ.P A A/2= jet (finances Z Γ) 2 A): PowerSeries.mk (Orb.diagonalWith U (Orb.restrictedO O)) = GermLaplace.Invoice.power V Λ (finances Z Γ) (volumeK Z U O) * (GermLaplace.Invoice.power V Λ (finances Z Γ) (volumeK Z U 1))⁻¹:= by
     rw [← sol_any Λ (spending_gap Z hn Γ) h]; exact (fp_order Z U H hn hp he Γ V).trans (GermLaplace.Invoice.remains V (spending_gap Z hn Γ) (earned_one Z U H hn Γ V).ne' _)
omit hp he H hn
-- a concrete PD parameter law if desired. (applies irrespective of the slice, not assuming
-- this particular smoothing reproduces the Landau strict-gauge **propagator**.)
def stream_cost (G:Gauge)(n:Side)(c:ℝ)(hc:0<c) : Law (Root (rim n) G):= pd (c • Trans.ℓ G n) (fun x y=> congr_arg (c • ·) (Trans.ghost_turn G n x y)) (fun x hx=> mul_pos hc (Trans.pos_ghost G n x hx))

/- specify the actual cost on values in `W`, not after basis normalization on `Root`. -/
variable {W : Type} [NormedAddCommGroup W][NormedSpace ℝ W][FiniteDimensional ℝ W]
def matchW (R:Cone G n→ₗ[ℝ] W)(h:Bijective (R ∘ₗ d G (rim n)))(Y : Law W): Law (Root (rim n) G):= Splice.focusWith Y (Repoint.chart R h).toLinearMap (Repoint.chart R h).injective
lemma paid_W (R:Cone G n→ₗ[ℝ] W)(h:Bijective (R ∘ₗ d G (rim n)))(Y : Law W)(A:Cone G n): finances (Repoint.issue G (staple n) R h) (matchW R h Y) A= pricing G n A + Rates.value Y (R A):= by
     unfold finances; rw [Repoint.reissue]; change pricing G n A + Rates.value Y (Repoint.chart R h ((Repoint.chart R h).symm (R A)))=_; rw [LinearEquiv.apply_symm_apply]
lemma jac_W (R:Cone G n→ₗ[ℝ] W)(h:Bijective (R ∘ₗ d G (rim n)))(A:Cone G n): AP (Repoint.issue G (staple n) R h) A= LinearMap.det ((Repoint.chart R h).symm.toLinearMap ∘ₗ R ∘ₗ directed G (rim n) A):= by unfold AP Aghost; rw [Repoint.reissue]; rfl

end FP
end Wilson
end YM.FVA2
