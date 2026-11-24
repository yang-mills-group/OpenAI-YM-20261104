import YM.Integration.WilsonUniformUnmarkedAffineMoment
import YM.MSbar.CrossH.Stout

/-! The registered finite first-anchor norm controls the actual
translation-rooted kinetic Hessian at its full finite spatial width,
including every separation on the observing torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonUniformUnmarkedHessianRow
open Filter Real Function Finset PowerSeries Lattice RG Wilson Tree Stationary Push.Uniform Bloch Exterior Precision
open FormalBulk08 Jets Flat Reef Mesa Lava Shore Lotus Wine Bank Orb Next.Free Series
open PhysicalNext.Repeat.Legato MSbar MSbar.Heath MSbar.Rolling MSbar.Cacao MSbar.Midpoint MSbar.Bakery
open RG16 RG16.Literal Pert.Asymptotics
open WilsonConditionalTaylorCourseAttachment WilsonConditionalTaylorBulkHistory
open WilsonMovingPolynomialPull
open scoped Classical Topology BigOperators ContDiff Matrix

variable {G : Gauge} {n : Side} {I : Type} [Fintype I] [DecidableEq I]

theorem derivative (P : MvPolynomial I ℝ) (i j : I) :
    Whisk.read 0 [j] (MvPolynomial.pderiv i P)=2*marble 2 P ![j,i] := by
  let f:=CrossH.clue P
  have smooth : ContDiffAt ℝ (↑(2:ℕ)) f 0 :=(Cacao.vent P).contDiffAt.of_le le_top
  have deriv:=CrossH.chain f [j,i] 2 0 smooth (by simp)
  have row:=congrFun (WilsonConditionalTaylorFiniteHessian.tensor P 2) ![j,i]
  change ((2:ℕ).factorial:ℝ)⁻¹*iteratedFDeriv ℝ 2 f 0 (dotI ∘ ![j,i])=marble 2 P ![j,i] at row
  have axes : (fun b : Fin ([j,i] : List I).length => (Push.Uniform.bolt (([j,i]:List I).get b))) =
      dotI ∘ ![j,i] := by funext b;fin_cases b <;> rfl
  rw [axes] at deriv
  rw [←Whisk.read_next 0 i [j] P,Whisk.read_perm (List.Perm.swap j i []),
    ←CrossH.tours 0 P [j,i]]
  change Lis.buoy f 0 [j,i]=_
  rw [deriv]
  change iteratedFDeriv ℝ 2 f 0 (dotI ∘ ![j,i])=2*marble 2 P ![j,i]
  norm_num at row
  linarith only [row]

def selected (n : Side) (u : G.ColorIndex) (x : Site n) := MSbar.Wave.primary (x,(1:Axis)) u

def hessian (n : Side) (u : G.ColorIndex) (A : Pap (wire G n)) (e : ℕ) (x : Site n) :=
  2*rancho A e 2 ![(x,coord (1:Axis),u),(0,coord (1:Axis),u)]

private theorem pair (A : Pap (wire G n)) (u : G.ColorIndex) (x : Site n) (e : ℕ) (positive : 0<e) :
    2*marble 2 (coeff e (WilsonConditionalTaylorRawAttachment.stored A))
      ![selected n u x,selected n u 0] = hessian n u A e x := by
  unfold WilsonConditionalTaylorRawAttachment.stored hessian
  rw [WilsonConditionalTaylorFieldReset.positive _ positive]
  congr 1
  let E:=WilsonMovingGaussianCoordinates.link G n
  change marble 2 (MvPolynomial.rename E.symm (coeff e A)) _=_
  rw [Shore.pebble,Shore.cores_once]
  change marble 2 (coeff e A) (E ∘ _) = _
  apply congrArg (marble 2 (coeff e A))
  funext z;fin_cases z <;> rfl

theorem row (A : Pap (wire G n)) (u : G.ColorIndex) (s e : ℕ) (positive : 0<e) {σ : ℝ} (width : 0 ≤ σ) :
    ∑ x : Site n, Whisk.liftW σ s (pdist x)*|hessian n u A e x| ≤
      CrossH.cog (Measuring.chart n G) σ s (coeff e (WilsonConditionalTaylorRawAttachment.stored A))
        1 (selected n u 0) := by
  let l:=Measuring.chart n G
  let f:=coeff e (WilsonConditionalTaylorRawAttachment.stored A)
  let h:=selected n u
  let o:=h 0
  let fee (i : Primary n G):=Whisk.rate l {l o} σ s 0 (MvPolynomial.pderiv o f) [i]
  have nonneg (i) : 0 ≤ fee i :=Whisk.liquid ..
  have inject : Injective h :=by intro x y hxy;exact congrArg l hxy
  have entry (x : Site n) : Whisk.liftW σ s (pdist x)*|hessian n u A e x| ≤ fee (h x) := by
    have here : l (h x) ∈ Whisk.zone l {l o} [h x] :=by simp [Whisk.zone]
    have there : l o ∈ Whisk.zone l {l o} [h x] :=by simp [Whisk.zone]
    have span:=Whisk.curve here there
    change separation x 0 ≤ _ at span
    simp only [separation,sub_zero] at span
    unfold fee Whisk.rate Whisk.spread
    rw [derivative, pair A u x e positive]
    exact mul_le_mul_of_nonneg_right (Whisk.w_more span width s) (abs_nonneg _)
  calc
    _ ≤ ∑ x : Site n, fee (h x) :=Finset.sum_le_sum (fun x _=>entry x)
    _ = ∑ i ∈ Finset.univ.image h,fee i := (Finset.sum_image (fun x _ y _ eq=>inject eq)).symm
    _ ≤ ∑ i : Primary n G, fee i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>nonneg i)
    _ = _ :=rfl

variable (R : Run G) (simple : G.Simple) (u : G.ColorIndex) (V : Voice G)
variable (bought : WilsonConditionalTaylorPurchase.Inventory u V R.kit)
variable (wood : ∀ j,Lodge (R.family.path.levels.clock.op j 0).patch)
variable (tags : ∀ j n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)

include bought simple in
theorem earned (s p : ℕ) (hs : 6 ≤ s) {η : ℝ} (fee : 0<η) :
    ∀ᶠ k : ℕ in atTop, ∀ N per, k ≤ N → ∀ j, k ≤ j → j ≤ N → ∀ e, 0<e → e ≤ p →
      let n:=R.family.side j per
      let A:=course R u wood tags N j n
      let σ:=Alto.candles R.family.path.levels j
      (∑ x : Site n, Whisk.liftW σ s (pdist x)*|hessian n u A e x|) ≤
        (regulatorRun R.family N per j)^(-η) := by
  filter_upwards [WilsonUniformUnmarkedFiniteStrip.anchored R simple u V bought wood tags s p hs fee]
    with k bond N per kN j lo hi e positive cap
  intro n A σ
  have width : 0 ≤ σ := by unfold σ Alto.candles Alto.cWidth; positivity
  exact (row A u s e positive width).trans (bond N per kN j lo hi e cap 1 (by omega) _)

end YM.Integration.WilsonUniformUnmarkedHessianRow
