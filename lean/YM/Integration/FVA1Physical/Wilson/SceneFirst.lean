import YM.Integration.FVA1Physical.Wilson.SceneBridge
import YM.Comparison.RG02.Bare.View
import YM.Integration.MSMatch.SourceTop

/-! The entire pre-reset vacuum polynomial at the first non-bare level.
The local Wilson action is centered exactly as in the realized vacuum
scene. The proof compares their separate expansions of the same Haar push. -/
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson

open Function Filter Finset RG Lattice YM.Wilson Exterior Tree Marker Comparison.RG02
open PertExtension.Series PertExtension.Series.Tested MSbar MSbar.Bakery MSbar.Bakery.Portal
open MSbar.Rolling MSbar.Wave MSbar.Midpoint Push Push.Uniform Precision
open scoped Classical BigOperators Topology

variable {G : Gauge} {c f : Side} {T : StepData c f} {p q : Clip}
    {P Q : PathData G} {O : ChartRatio G} (K : Bulk.Kernel T p P O)
    {V : Type} [Fintype V] [DecidableEq V] {R : Census V} (W : Bulk.Colors R G f)
    (B : Forest T.ratio) (u : T.Choices) (r : ℕ)

private theorem log_relative_push (g : ℝ) (hg : 0 < g) (x : fieldDir G c 1) :
    Real.log (shunt T (breed G f) g (Integral.sample g x)) =
      Real.log (Bare.rho K B u x g) - Real.log (Bare.rho K B u 0 g) +
        ((Symmetry.price K B u x).re - (Symmetry.price K B u 0).re) := by
  let a (z : fieldDir G c 1) :=
    T.push (Integral.temperature g) (bare (Integral.temperature g)) (Integral.sample g z)
  let v (z : fieldDir G c 1) := Integral.office K B u g 0 z
  have ha z : 0 < a z := Normal.total_pos T _ _ _ (Bare.bare_enough g) K.branches
  have hv z : 0 < v z := Integral.office_pos K B u g 0 z hg
  have eqn (z : fieldDir G c 1) :
      Real.log (Bare.rho K B u z g) = Real.log (a z) - Real.log (v z) := by
    change Real.log ((v z)⁻¹ * a z) = _
    rw [Real.log_mul (inv_ne_zero (hv z).ne') (ha z).ne', Real.log_inv]
    ring
  have slope (z : fieldDir G c 1) :
      Real.log (v z) =
        Real.log (Next.SectorChange.chartCost (K.covariance B u) g) +
          Real.log (Integral.tab (F := B) (O := O)) +
          Real.log (Next.Fluctuations.Sector.prefactor T G (Integral.temperature g)) +
          (Symmetry.price K B u z).re := by
    have ht : 0 < Integral.tab (F := B) (O := O) := pow_pos K.ratio.scale _
    have hp : 0 < Next.Fluctuations.Sector.prefactor T G (Integral.temperature g) :=
      Next.Fluctuations.Sector.prefactor_pos _
    have hc := Next.SectorChange.chartCost_pos _ (K.positive B u) hg
    unfold v Integral.office Integral.standard Integral.calorie
    rw [Real.log_mul hc.ne' (mul_pos (mul_pos ht hp) (Real.exp_pos _)).ne',
      Real.log_mul (mul_pos ht hp).ne' (Real.exp_pos _).ne',Real.log_mul ht.ne' hp.ne',
      Real.log_exp]
    simp only [Symmetry.price,Complex.neg_re,Complex.ofReal_re,zero_sub]
    ring
  have ht : g⁻¹^2 = Integral.temperature g := inv_pow g 2
  have hz : Integral.sample g (0 : fieldDir G c 1) = 1 := by simp [Integral.sample]
  rw [shunt_is_physical,breed,ht,← hz]
  change Real.log (a x / a 0) = _
  rw [Real.log_div (ha x).ne' (ha 0).ne',eqn,eqn,slope,slope]
  ring

private theorem trial_real {A : ℕ → ℂ} {F : ℝ → ℝ} {r : ℕ}
    (h : Laplace.Trial A (fun g => (F g : ℂ)) r) :
    Bill (r+1) (fun g => F g - ∑ i ∈ range (r+1), g^i * (A i).re) := by
  obtain ⟨b,hb,est⟩ := h
  refine ⟨b,hb,est.mono fun g hg => ?_⟩
  refine le_trans ?_ hg
  have e : ((F g : ℂ) - peval A r g).re =
      F g - ∑ i ∈ range (r+1), g^i * (A i).re := by
    rw [Complex.sub_re,Complex.ofReal_re]
    exact congrArg (F g - ·) (RGComparison.Core16.WilsonXLocal.eval_map (a:=A) (r:=r) Complex.reCLM g).symm
  change ‖F g - ∑ i ∈ range (r+1), g^i * (A i).re‖ ≤ ‖(F g : ℂ) - peval A r g‖
  rw [← e,Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

/-- The all-order bound on the origin-normalized physical Haar push uses the
independent Wilson action at the chosen coarse field minus its value at the
identity. It holds before any formal coupling retuning. -/
theorem first_centered_vacuum_price (D : BudgetPoint) (hW : Bare.Witnessed W K)
    (x : fieldDir G c 1) :
    Bill (r+1) (fun g => Real.log (shunt T (breed G f) g (Integral.sample g x)) -
      ∑ i ∈ range (r+1), g^i *
        ((Symmetry.Orbit.ground K B u W r i x).re - (Symmetry.Orbit.ground K B u W r i 0).re)) := by
  let coefficients (z : fieldDir G c 1) := Laplace.detail (Order.logVac (Bulk.Fk K B u W z r)) R.quiet
  let e (z : fieldDir G c 1) (g : ℝ) :=
    Real.log (Bare.rho K B u z g) - ∑ i ∈ range (r+1), g^i * (coefficients z i).re
  have he (z : fieldDir G c 1) : Bill (r+1) (e z) :=
    trial_real (Bare.wilson_step_test K B W u z r D hW).2.1
  have sum (g : ℝ) (z : fieldDir G c 1) :
      ∑ i ∈ range (r+1), g^i * (Symmetry.Orbit.ground K B u W r i z).re =
      (∑ i ∈ range (r+1), g^i * (coefficients z i).re) + (Symmetry.price K B u z).re := by
    simp only [Symmetry.Orbit.ground,Complex.add_re,apply_ite Complex.re,Complex.zero_re,
      mul_add,mul_ite,mul_zero,Finset.sum_add_distrib, Finset.sum_ite_eq',Finset.mem_range,
      Nat.zero_lt_succ,if_true,pow_zero,one_mul,coefficients]
  refine Laplace.bill_congr ?_ (bill_add (he x) (bill_neg (he 0)))
  filter_upwards [eventually_pos] with g hg
  simp only [Pi.add_apply,Pi.neg_apply,e]
  rw [log_relative_push K B u g hg]
  simp_rw [mul_sub,Finset.sum_sub_distrib]
  rw [sum,sum]
  ring

private theorem scene_prediction {S : Nesting G c} {F : ℝ → Config G c → ℝ}
    (h : Trend F S Q q r) (x : Positions (Primary c G)) :
    Wave.Grade (fun g => Real.log (F g (postcard G c g x)) -
      ∑ i ∈ range (r+1), g^i * Lis.atlas S r i Q q x) (r+1) := by
  have hx : ∀ᶠ g in Laplace.along, yard 1 g x :=
    (awake.eventually_ge_atTop ‖x‖).mono fun g hv => by simpa [yard] using hv
  apply (Rolling.Price.inherits (V:=fun _ (_:Unit) => True) (h.tune 1)
    (fun _ _ => x) (hx.mono fun _ hv _ _ => hv)).egress
  filter_upwards with g _ _
  have eqn := tariff_data r q Q S h x r g
  unfold taste picture at eqn
  simp only [PowerSeries.coeff_map] at eqn
  unfold taste picture Lis.atlas Wave.joy
  simp only [PowerSeries.coeff_map]
  linarith only [eqn]

/-- Independent coefficient identity before retuning. The scene must describe
the stated physical push; a realized local step supplies this genuine analytic
property from its fine input. Neither series is defined using the other. -/
theorem first_scene_identification (D : BudgetPoint) (hW : Bare.Witnessed W K)
    {S : Nesting G c} (h : Trend (shunt T (breed G f)) S Q q r)
    (x : Positions (Primary c G)) {i : ℕ} (hi : i ≤ r) :
    let z := tint G (Body 1 c) x
    Lis.atlas S r i Q q x =
      (Symmetry.Orbit.ground K B u W r i z).re - (Symmetry.Orbit.ground K B u W r i 0).re := by
  let z := tint G (Body 1 c) x
  let A i := (Symmetry.Orbit.ground K B u W r i z).re - (Symmetry.Orbit.ground K B u W r i 0).re
  let T' i := Lis.atlas S r i Q q x
  have hP (g : ℝ) : postcard G c g x = Integral.sample g z := by
    simp only [postcard,Integral.sample,map_smul,z]
  obtain ⟨b,_,est⟩ := first_centered_vacuum_price K W B u r D hW z
  have hp : Wave.Grade (fun g => Real.log (shunt T (breed G f) g (postcard G c g x)) -
      ∑ l ∈ range (r+1),g^l * A l) (r+1) := by
    apply Rolling.Price.fixed 0 b
    filter_upwards [est] with g hg _ _
    simpa [hP,A,pow_zero] using hg
  have ht := scene_prediction (r:=r) h x
  apply sub_eq_zero.mp
  apply Wave.magnitude (f:=fun k => T' k - A k) (n:=r) _ i hi
  apply (hp.cut ht).egress
  filter_upwards with g _ _
  simp only [mul_sub,Finset.sum_sub_distrib,T']
  ring

end YM.Integration.FVA1Physical.Wilson
