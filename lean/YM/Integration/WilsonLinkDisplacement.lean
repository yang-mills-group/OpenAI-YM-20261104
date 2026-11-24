import YM.Integration.WilsonEnergySecant
import YM.Integration.WilsonMatrixInversion
import YM.Integration.WilsonTaggedLinkExpansion

/-! All moments of the displacement of a measured Wilson link, uniformly in its prediction. -/
noncomputable section
namespace YM.Integration.WilsonLinkDisplacement
open YM RG RG02 RG02.Asym Lattice Wilson Filter MeasureTheory
open PertExtension.Series PertExtension.Series.Tested WilsonKernelCoupling
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} (S : StepData c f)

def amplitude (G : Gauge) (n : ℕ) (g : G.El) : ℝ := ‖G.mat g-1‖^n

def rate (G : Gauge) (κ : ℝ) : ℝ := (3/4:ℝ)*κ/(2*(G.repDim:ℝ))

def price (G : Gauge) (κ : ℝ) (n : ℕ) : ℝ := 1+(n.factorial:ℝ)/(rate G κ)^n

theorem rate_pos (G : Gauge) {κ : ℝ} (hκ : 0 < κ) : 0 < rate G κ := by
  have hd : 0 < (G.repDim:ℝ) := by exact_mod_cast G.dimPos
  unfold rate
  positivity

theorem price_pos (G : Gauge) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) : 0 < price G κ n := by
  have hr := rate_pos G hκ
  unfold price
  positivity

theorem dominate (G : Gauge) {κ t : ℝ} (hκ : 0 < κ) (ht : 0 < t) (n : ℕ) (g : G.El) :
    amplitude G n g ≤ (t^n*price G κ n) *
      Real.exp ((((t^2)⁻¹-((2*t)^2)⁻¹)*κ)*G.price g) := by
  let x := ‖G.mat g-1‖/t
  let h := rate G κ
  let K := (n.factorial:ℝ)/h^n
  have hh : 0 < h := rate_pos G hκ
  have hd : 0 < (G.repDim:ℝ) := by exact_mod_cast G.dimPos
  have hs : h*x^2 = (((t^2)⁻¹-((2*t)^2)⁻¹)*κ)*G.price g := by
    dsimp only [h,rate,x]
    rw [div_pow,WilsonMatrixInversion.square]
    field_simp [hd.ne',ht.ne']
    ring
  have hsquare : (x^2)^n = (x^n)^2 := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
  have hpower : x^n ≤ 1+(x^2)^n := by
    rw [hsquare]
    nlinarith only [sq_nonneg (x^n-1/2)]
  have htaylor : (x^2)^n ≤ K*Real.exp (h*x^2) :=
    WilsonLocalKernelMoments.power (sq_nonneg x) hh n
  have he : 1 ≤ Real.exp (h*x^2) := Real.one_le_exp (mul_nonneg hh.le (sq_nonneg x))
  have hn : x^n ≤ (1+K)*Real.exp (h*x^2) :=
    hpower.trans ((add_le_add he htaylor).trans_eq (by ring))
  have hm : t*x = ‖G.mat g-1‖ := by dsimp only [x]; field_simp
  calc
    amplitude G n g = t^n*x^n := by rw [← mul_pow,hm,amplitude]
    _ ≤ t^n*((1+K)*Real.exp (h*x^2)) := mul_le_mul_of_nonneg_left hn (pow_nonneg ht.le n)
    _ = _ := by rw [hs]; change _ = t^n*(1+K)*_; ring

theorem bound {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (∫ g : G.El, link S (t^2)⁻¹ 1 g * amplitude G n g ∂G.probHaar) ≤
      (t^n*price G S.kernel.penalty n) * (S.penaltyZ ((2*t)^2)⁻¹ G / S.penaltyZ (t^2)⁻¹ G) := by
  let b := (t^2)⁻¹
  let h := b-((2*t)^2)⁻¹
  let A := t^n*price G S.kernel.penalty n
  have hl : Continuous (link S b (1:G.El)) := by unfold link StepData.penaltyWeight; fun_prop
  have he : Continuous (fun g : G.El => Real.exp ((h*S.kernel.penalty)*G.price g)) :=
    Real.continuous_exp.comp (continuous_const.mul G.continuous_price)
  have hi := (hl.mul he).integrable_of_hasCompactSupport (μ:=G.probHaar) (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ g : G.El, A*(link S b 1 g * Real.exp ((h*S.kernel.penalty)*G.price g)) ∂G.probHaar := by
      apply integral_mono_of_nonneg (ae_of_all _ fun g => mul_nonneg (link_pos S b 1 g).le (pow_nonneg (norm_nonneg _) _)) (hi.const_mul _)
      apply ae_of_all
      intro g
      have H := mul_le_mul_of_nonneg_left (dominate G S.kernel.penalty_pos ht n g) (link_pos S b 1 g).le
      exact H.trans_eq (mul_left_comm (link S b 1 g) A (Real.exp ((h*S.kernel.penalty)*G.price g)))
    _ = _ := by rw [integral_const_mul,WilsonLinkEnergy.tilt]; dsimp only [h,b,A]; rw [sub_sub_cancel]

theorem coordinate (e : Edge (Site c)) (b : ℝ) (Q : Config G c) (n : ℕ) :
    (∫ V, S.noise b Q V * amplitude G n (V e*(Q e)⁻¹) ∂prior G c) =
      ∫ g, link S b 1 g * amplitude G n g ∂G.probHaar := by
  let a : ↥({e} : Finset (Edge (Site c))) := ⟨e,by simp⟩
  have hu : (Finset.univ : Finset (↥({e} : Finset (Edge (Site c))))) = {a} := by
    ext i
    simp only [Finset.mem_univ,Finset.mem_singleton,true_iff]
    exact Subtype.ext (Finset.mem_singleton.mp i.property)
  have H := WilsonSmoothCylinder.expectation S {e} b Q (fun _ v => amplitude G n (v*(Q e)⁻¹))
  simp only [hu,Finset.prod_singleton,a] at H
  exact H.trans (WilsonTaggedLinkExpansion.translate S b (Q e) (amplitude G n))

/-- The same temperature tail prices every moment, every edge, and every predicted configuration. -/
theorem calendar (D : Calendar G) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧ ∀ᶠ t in Tested.germ, ∀ n m p : ℕ,
      ∀ (e : Edge (Site (D.schedule.side m p))) (Q : Config G (D.schedule.side m p)),
        (∫ V, (D.op m p).noise (t^2)⁻¹ Q V * amplitude G n (V e*(Q e)⁻¹) ∂prior G _) ≤ C n*t^n := by
  let d := Friction.cardinal G
  let B := (2:ℝ)^d+1
  have hB : 0 < B := by dsimp only [B]; positivity
  have H := (WilsonEnergySecant.real_ratio (D.op 0 0) G (r:=2) (by norm_num)).eventually
    (eventually_lt_nhds (lt_add_one ((2:ℝ)^d)))
  refine ⟨fun n => price G D.kernel.penalty n*B,fun n =>
    mul_nonneg (price_pos G D.kernel.penalty_pos n).le hB.le,?_⟩
  filter_upwards [H,Tested.eventually_pos] with t hratio ht n m p e Q
  rw [coordinate]
  have hr : (D.op m p).penaltyZ ((2*t)^2)⁻¹ G / (D.op m p).penaltyZ (t^2)⁻¹ G ≤ B := hratio.le
  exact (bound (D.op m p) ht n).trans ((mul_le_mul_of_nonneg_left hr
    (mul_nonneg (pow_nonneg ht.le n) (price_pos G D.kernel.penalty_pos n).le)).trans_eq (by ring))

end YM.Integration.WilsonLinkDisplacement
