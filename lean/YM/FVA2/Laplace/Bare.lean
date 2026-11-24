import YM.FVA2.Laplace.Receipt
import YM.FVA2.Orbit.TreeChoice
import YM.PertExtension.Normalized
/-!
# Evaluate the complete Wilson bare coefficient in any of the rooted strict gauges

Here use any permitted analytic (strict, complementary-to-orbit) gauge with invertible tangent
`tilt`; see `Screen` for the condition. The recipe with its Jacobian, the same Wilson action
with its overall factor 1/2, and the covariance from the Hessian gives the same answer for every
relevant joint probe. We can use linear tree gauge; another physical application is the Landau
slice in comparing with `Master G n true`.

The gauge-independence calculation uses `genuine`, `realization` and
`realization_exists` for the Gaussian law, and `Folio.external` for the
external powers. The Feynman-gauge calculation in `Feyn/Canonical.lean`
preserves these readings under its ROOT convention before the Landau slice.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Orbit
open Function Set Filter Finset MeasureTheory Measure PertExtension PertExtension.Orb Laplace Wilson Lattice
open FormalOPE.RG10.MultiGauge Splice PertExtension.GaussianScore
open Series Radial Series.Tested
open scoped ContDiff Topology Classical BigOperators
variable {G:Gauge}{n:Side} {E F:Type}
 [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
namespace Screen
local notation "P" => Config G n
local notation "T" => Site n
variable (s:Screen G n E)(u:Screen G n F)
/-- Same projected Wilson action. -/
def price (x:E) := Wilson.energy (Orbit.ignite (s.σ x))/2
/-- Same physical observable articulated in exponential chart. -/
def play (O:Config G n→ℝ) (x:E) := O (Orbit.ignite (s.σ x))
lemma transition : Jacobs (s.reform u) (s.rework u):= ⟨s.reform_hot u,s.reform_zero u,(s.rework_eq u).symm⟩
lemma cover : ∀ᶠ x in 𝓝 0, ignite (s.σ x)= Lattice.gauge (gang (s.Δ u x)) (ignite (u.σ (s.reform u x))):= by
    filter_upwards [ (tup (aimed (s.Δ_hot u).continuousAt (s.Δ_zero u)) ((u.σ_tends).comp (s.transition u).forwards)).eventually physical,s.gauge_change u] with x hx he; rw [he]; exact hx
lemma cost : s.price=ᶠ[𝓝 0] u.price ∘ (s.reform u):= by filter_upwards [s.cover u] with x hx; unfold price; rw [hx, energy_gauge]; rfl
variable {O:Config G n→ℝ}
lemma evaluates (p:Orb.PreTest O) : s.play O=ᶠ[𝓝 0] u.play O ∘ s.reform u:= by filter_upwards [s.cover u] with x hx; unfold Screen.play; rw [hx,p.gauge _ (gang_neg _)]; rfl
variable (ev:Even n.val)
local notation "J" => Dir G n
local notation "y" => Grove.rooted G ev
lemma tree_price : (Grove.rooted G ev).price= Orb.fiscal:= by funext x; unfold price fiscal; rw [show ignite ((y).σ x)=_ from Grove.tree_ignite x]
lemma tree_play (O:P→ ℝ) : (y).play O= (Orb.restrictedO O) ∘ Chart.expLinks G (Cotree n):= by funext x; unfold play; rw [show ignite ((y).σ x)= _ from Grove.tree_ignite x]; rfl
lemma tree_hair : (y).weight=ᶠ[𝓝 0] hair:= Grove.shrub_cost PertExtension.Orb.Branch (Grove.permitted ev)
include ev
/-- Existence of quadratic bound (hence the `Law`, later). -/
theorem viable : Steep s.price:= by
    have hp: Steep (Orb.fiscal (n:=n) (G:=G)):= ⟨Orb.fiscal_stationary,Orb.coercion ev⟩
    have he:= (s.transition y).steepens hp; apply he.germ; rw [← tree_price ev]; exact (cost ..).symm
lemma hearing (p:Orb.PreTest O): ContDiffAt ℝ ∞ (s.play O) 0:= by
 let k:=s.reform y; have hp:ContDiffAt ℝ ∞ ((y).play O) 0:= by rw [tree_play]; exact p.curved.germ
 exact ((s.reform_zero y |>.symm ▸ hp : ContDiffAt ℝ ∞ ((y).play O) (s.reform y 0)).comp (f:=k) 0 ((s.reform_hot y).of_le le_top)).congr_of_eventuallyEq (s.evaluates y p)
variable [MeasurableSpace E][BorelSpace E][MeasurableSpace F][BorelSpace F]
variable (μ:Measure E)[μ.IsAddHaarMeasure](ν:Measure F)[ν.IsAddHaarMeasure]
/-- Normalized same scalar series in this strict gauge. -/
def charge (O:P→ℝ) := pricetag μ s.weight s.price (s.play O)
lemma same_scalar (p:Orb.PreTest O) : s.charge μ O=u.charge ν O:= by
 let k:=s.transition u
 have hf:Steep u.price:= u.viable ev
 let c:=Jacobs.amount (s.rework u) μ ν
 have hA := s.cost u
 unfold charge pricetag; refine shed2 c ?_ ?_ (ready ν hf u.head) (Jacobs.pay_pos ..)
 · unfold Laplace.rows; rw [k.moment_change μ ν hf hA (K':=u.play O * u.weight) ((u.hearing ev p).mul (u.analytic.of_le le_top)), up]; filter_upwards [s.meter_change u,s.evaluates u p] with x hx hv; simp only [Function.comp_apply] at hv; rw [Pi.mul_apply,hx,hv,Pi.mul_apply];ring
 unfold Laplace.rows; rw [ k.moment_change μ ν hf hA (u.analytic.of_le le_top), up]; exact (s.meter_change u).mono (fun x hx=> hx.trans (mul_comm ..))
-- compare to fixed Orb tree gauge row including density normalization
local notation "μ₀" => Chart.tangent G (Cotree n)
variable {K:Precision.ChartRatio G}(k:Precision.LocalRatio K)
private def factor (K:Precision.ChartRatio G)(n:Side) := K.scale ^ Fintype.card (Cotree n)
include k
omit ev in
private lemma fees : ∀ᶠ x:G.Color in 𝓝 0, Chart.fee K x=K.scale*LocalH.spin G x:= by
 filter_upwards [MS.Bare.Maurer.real_ratio k,spin_pos (G:=G)] with x hx hz; rw [Chart.fee,hx,max_eq_left (mul_nonneg k.scale.le hz.le)]
private lemma tree_accounting (O:P→ℝ): Orb.accountingWith K (Orb.restrictedO O) =ᶠ[𝓝 0] factor K n • ((y).play O * (y).weight):= by
 filter_upwards [tree_hair (G:=G) ev,eventually_all.mpr (fun i:Cotree n=> (continuous_apply i|>.tendsto (0:J)).eventually (fees k))] with x hx hy
 change Chart.jacobian K x * _=factor K n* (_ * _); rw [hx]; unfold Chart.jacobian; simp_rw [hy,prod_mul_distrib,prod_const,card_univ]; unfold hair factor; rw [mul_right_comm, mul_comm,tree_play,comp_apply]; ring
omit k ev in
private lemma moment_smul {a:J→ℝ}(c:ℝ)(p:ContDiffAt ℝ ∞ a 0): Radial.moment μ₀ (c • a) fiscal=c • Radial.moment μ₀ a fiscal:= by
    have ht(i:ℕ)(u:J) : jet (c • a) i u=c*jet a i u:= by unfold jet; rw [iteratedFDeriv_const_smul_apply (hf:=p.of_le (m:=(i:WithTop ℕ∞)) (by exact WithTop.coe_le_coe.mpr le_top))]; simp only [_root_.smul_apply]; simp only [smul_eq_mul]; ring
    funext k; unfold Radial.moment; change _= c * _; rw [← integral_const_mul]
    congr 1; ext x; unfold normTerm integrandSeries Zone.mul; simp_rw [ht,mul_assoc]; rw [←Finset.mul_sum]; ring
lemma carry_tree (O:Config G n → ℝ) (p:Orb.PreTest O): Orb.rowsWith (n:=n) K (Orb.restrictedO O)= factor K n • Radial.moment μ₀ ((y).play O * (y).weight) (y).price:= by
 rw [tree_price]; unfold Orb.rowsWith; rw [Laplace.replace μ₀ (EventuallyEq.refl (𝓝 0) fiscal) (tree_accounting ev k O),moment_smul (a:=(y).play O * (y).weight) (p:= ((y).hearing ev p).mul ((y).analytic.of_le le_top))]
omit k
omit ev in
lemma pre_one : Orb.PreTest (1:P→ℝ):= ⟨fun _ _ _=>rfl,Orb.one_test,continuous_const⟩
lemma unit_cancel : (y).play 1 * (y).weight = (y).weight := by simp_rw [show (y).play 1=(1:J→ℝ) from rfl,one_mul]
include k
lemma kept_tree (p:Orb.PreTest O): PowerSeries.mk (Orb.diagonalWith K (Orb.restrictedO O)) = (y).charge μ₀ O:= by
    change PowerSeries.mk (Series.Tested.term (((PowerSeries.mk (Orb.rowsWith _ _))*((PowerSeries.mk (Orb.rowsWith K (n:=n) 1))⁻¹)))) = _
    rw [show ∀ z : PowerSeries ℝ, PowerSeries.mk (Series.Tested.term z)=z from (fun a=> PowerSeries.ext fun i=>by rw [PowerSeries.coeff_mk];rfl), carry_tree ev k O p, show (1:Observable G n)=Orb.restrictedO (1:P→ℝ) from rfl, carry_tree ev k (1:P→ℝ) pre_one, Laplace.up, Laplace.up, unit_cancel]; unfold charge pricetag; exact shed _ _ _ (ready μ₀ ((y).viable ev) (y).head) (pow_pos k.scale _)

omit k
/-- Full, normalized (using the gauge invariant probe itself, e.g. the product of
its physical stencils). Before external powers are reattached. See `Arrival/Folio.lean` to also
prove the Laurent shift equations. -/
theorem genuine (p : Orb.PreTest O) :
        s.charge μ O = PowerSeries.mk (Orb.diag (Orb.restrictedO O)) :=
    (s.same_scalar y ev μ μ₀ p).trans (kept_tree ev (Orb.traySpec G) p).symm

lemma realization (Λ:Law E) (hk:Λ.kern=Radial.kernel s.price) (p:Orb.PreTest O) :
        s.charge μ O = Splice.enjoy Λ μ (Stack.rise (s.play O)) (sink s.weight s.price) :=
    Laplace.receipt μ Λ hk s.head (s.analytic.of_le le_top) (s.hearing ev p)
omit [BorelSpace E] in
lemma realization_exists : (s.viable ev).law.kern= Radial.kernel s.price:= (s.viable ev).law_eq
end Screen
end YM.FVA2.Orbit
