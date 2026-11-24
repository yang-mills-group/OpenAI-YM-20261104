import YM.Integration.WilsonWalkMatrixSecant
import YM.Integration.WilsonLinkEnergy
import YM.Integration.WilsonPhysicalKernelClock
import YM.Integration.WilsonSmoothCylinder

/-! Quadratic bias of the signed matrix holonomy of every finite Wilson walk
under the original translated branch law and its physical mixture. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWalkMatrixBias
open RG Lattice Wilson MeasureTheory Filter
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open FullQLocal.RenderedStep MatchingLedger.Compass.Income
open WilsonKernelCoupling WilsonWalkMatrixSecant
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} (S : StepData c f)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private theorem noise_cont (b : ℝ) (Q : Config G c) : Continuous (fun V : Config G c => S.noise b Q V) := by
  unfold StepData.noise StepData.penaltyWeight
  fun_prop

omit [CompleteSpace E] in
private theorem shifted (b : ℝ) (Q : Config G c) (F : Config G c → E) :
    (∫ V, S.noise b Q V • F V ∂prior G c) =
      ∫ g, S.noise b 1 g • F (g*Q) ∂prior G c := by
  have hm : MeasurePreserving (fun g : Config G c => g*Q) (prior G c) (prior G c) :=
    measurePreserving_pi _ _ (fun e => measurePreserving_mul_right G.probHaar (Q e))
  have hnoise (g : Config G c) : S.noise b Q (g*Q) = S.noise b 1 g := by
    simp only [StepData.noise,Pi.mul_apply,Pi.one_apply,inv_one,mul_one,mul_inv_cancel_right]
  have h := hm.integral_comp (Homeomorph.mulRight Q).measurableEmbedding (fun v => S.noise b Q v • F v)
  simpa only [hnoise] using h.symm

omit [CompleteSpace E] in
private theorem inverse (b : ℝ) (F : Config G c → E) :
    (∫ g, S.noise b 1 g • F g⁻¹ ∂prior G c) = ∫ g, S.noise b 1 g • F g ∂prior G c := by
  have hm : MeasurePreserving (Inv.inv : Config G c → Config G c) (prior G c) (prior G c) :=
    measurePreserving_pi _ _ (fun (_ : Edge (Site c)) => G.preserve_inv)
  have hnoise (g : Config G c) : S.noise b 1 g⁻¹ = S.noise b 1 g := by
    simp only [StepData.noise,Pi.inv_apply,Pi.one_apply,inv_one,mul_one,StepData.penaltyWeight,G.price_inv]
  have h := hm.integral_comp (MeasurableEquiv.inv (Config G c)).measurableEmbedding
    (fun g => S.noise b 1 g • F g)
  simpa only [hnoise] using h

theorem mean_edge (b : ℝ) (e : Edge (Site c)) :
    (∫ g : Config G c, S.noise b 1 g * G.price (g e) ∂prior G c) = WilsonLinkEnergy.energy S G b := by
  let a : ↥({e} : Finset (Edge (Site c))) := ⟨e,by simp⟩
  have hu : (Finset.univ : Finset (↥({e} : Finset (Edge (Site c))))) = {a} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subtype.ext (Finset.mem_singleton.mp i.property)
  have h := WilsonSmoothCylinder.expectation S {e} b (1 : Config G c) (fun _ v => G.price v)
  simpa only [hu,Finset.prod_singleton,a,Pi.one_apply,WilsonLinkEnergy.energy] using h

def priceSum (E : List (Edge (Site c))) (g : Config G c) : ℝ :=
  (E.map (fun e => G.price (g e))).sum

private theorem continuous_priceSum (E : List (Edge (Site c))) : Continuous (priceSum (G:=G) E) := by
  induction E with
  | nil => exact continuous_const
  | cons a l ih => exact (G.continuous_price.comp (continuous_apply a)).add ih

theorem mean_sum (b : ℝ) (E : List (Edge (Site c))) :
    (∫ g : Config G c, S.noise b 1 g * priceSum E g ∂prior G c) =
      (E.length : ℝ)*WilsonLinkEnergy.energy S G b := by
  letI : IsFiniteMeasureOnCompacts (prior G c) := inferInstanceAs
    (IsFiniteMeasureOnCompacts (Measure.pi (fun _ : Edge (Site c) => G.probHaar)))
  have hρ : Continuous (S.noise b (1 : Config G c)) := noise_cont S b 1
  induction E with
  | nil => simp [priceSum]
  | cons a l ih =>
    have ha := (hρ.mul (G.continuous_price.comp (continuous_apply a))).integrable_of_hasCompactSupport
      (μ:=prior G c) (HasCompactSupport.of_compactSpace _)
    have hl := (hρ.mul (continuous_priceSum (G:=G) l)).integrable_of_hasCompactSupport
      (μ:=prior G c) (HasCompactSupport.of_compactSpace _)
    change (∫ g, S.noise b 1 g * (G.price (g a)+priceSum l g) ∂prior G c) = _
    simp_rw [mul_add]
    rw [integral_add (f:=fun g : Config G c => S.noise b 1 g * G.price (g a))
      (g:=fun g : Config G c => S.noise b 1 g * priceSum l g) ha hl,mean_edge,ih,List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

/-- The true product noise at any fixed predicted configuration has quadratic
matrix-holonomy bias, uniformly in all orientations and link repetitions. -/
theorem conditional (L : G.Mat →L[ℝ] E) (K : ℝ) (hK : 0 ≤ K) (hL : ∀ X, ‖L X‖ ≤ K*‖X‖) (b : ℝ) (Q : Config G c) (x : Site c) (w : Walk) :
    ‖(∫ V, S.noise b Q V • L (G.mat (travel V x w)) ∂prior G c) - L (G.mat (travel Q x w))‖ ≤
      K * (w.length:ℝ)^2 * (G.repDim:ℝ) * WilsonLinkEnergy.energy S G b := by
  letI : IsFiniteMeasureOnCompacts (prior G c) := inferInstanceAs
    (IsFiniteMeasureOnCompacts (Measure.pi (fun _ : Edge (Site c) => G.probHaar)))
  let ρ := S.noise b (1 : Config G c)
  let F (g : Config G c) := L (G.mat (travel (g*Q) x w))
  let q := L (G.mat (travel Q x w))
  let l := occurrences x w
  let A : ℝ := K*(w.length:ℝ)*(2*(G.repDim:ℝ))
  have hp (g : Config G c) : 0 ≤ ρ g := Finset.prod_nonneg
    fun i _ => mul_nonneg (inv_pos.mpr (S.penaltyZ_pos b)).le (Real.exp_pos _).le
  have hρ : Continuous ρ := noise_cont S b 1
  have hF : Continuous F := L.continuous.comp (G.continuous_mat.comp ((continuous_travel w x).comp (continuous_id.mul continuous_const)))
  have ht (H : Config G c → E) (h : Continuous H) :
      Integrable (fun g => ρ g • H g) (prior G c) :=
    (hρ.smul h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmass : (∫ g, ρ g ∂prior G c) = 1 := S.noise_mass b 1
  have hrec : (∫ g, ρ g • F g⁻¹ ∂prior G c) = ∫ g, ρ g • F g ∂prior G c := inverse S b F
  have hsum : (∫ g, ρ g • ((F g-q)+(F g⁻¹-q)) ∂prior G c) =
      (2:ℝ) • ((∫ g, ρ g • F g ∂prior G c)-q) := by
    have cent (H : Config G c → E) (hh : Continuous H) :
        (∫ g, ρ g • (H g-q) ∂prior G c) = (∫ g, ρ g • H g ∂prior G c)-q := by
      simp only [smul_sub]
      rw [integral_sub (f:=fun g => ρ g • H g) (g:=fun g => ρ g • q)
        (ht H hh) (ht (fun _ => q) continuous_const),integral_smul_const,hmass,one_smul]
    simp only [smul_add]
    rw [integral_add (f:=fun g => ρ g • (F g-q)) (g:=fun g => ρ g • (F g⁻¹-q))
      (ht _ (hF.sub continuous_const)) (ht _ ((hF.comp continuous_inv).sub continuous_const)),
      cent F hF,cent (fun g => F g⁻¹) (hF.comp continuous_inv),hrec,two_smul]
  have hmajor (g : Config G c) : ‖ρ g • ((F g-q)+(F g⁻¹-q))‖ ≤ A*(ρ g*priceSum l g) := by
    rw [norm_smul, Real.norm_of_nonneg (hp g)]
    let X := (G.mat (travel (g*Q) x w) - G.mat (travel Q x w)) +
      (G.mat (travel (g⁻¹*Q) x w) - G.mat (travel Q x w))
    have hX : (F g-q)+(F g⁻¹-q) = L X := by simp only [F,q,X,map_add,map_sub]
    rw [hX]
    exact (mul_le_mul_of_nonneg_left ((hL X).trans
      (mul_le_mul_of_nonneg_left (secant g Q x w) (hK))) (hp g)).trans_eq
        (by dsimp only [A,l,priceSum]; ring)
  have hI : Integrable (fun g => ρ g • ((F g-q)+(F g⁻¹-q))) (prior G c) := ht _ ((hF.sub continuous_const).add ((hF.comp continuous_inv).sub continuous_const))
  have hJ : Integrable (fun g => A*(ρ g*priceSum l g)) (prior G c) := ((continuous_const (y:=A)).mul (hρ.mul (continuous_priceSum (G:=G) l))).integrable_of_hasCompactSupport
    (μ:=prior G c) (HasCompactSupport.of_compactSpace _)
  have hle := (norm_integral_le_integral_norm (μ:=prior G c) (fun g => ρ g • ((F g-q)+(F g⁻¹-q)))).trans
    (integral_mono hI.norm hJ hmajor)
  rw [hsum,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2),integral_const_mul,mean_sum] at hle
  rw [shifted S b Q (fun V => L (G.mat (travel V x w)))]
  change ‖(∫ g, ρ g • F g ∂prior G c)-q‖ ≤ _
  dsimp only [A,l] at hle
  rw [length_occurrences] at hle
  linarith only [hle]

/-- Original branch weights average the signed predicted walk on the same
fine configuration, with the same uniform polynomial length factor. -/
theorem mixture (L : G.Mat →L[ℝ] E) (K : ℝ) (hK : 0 ≤ K) (hL : ∀ X, ‖L X‖ ≤ K*‖X‖) (b : ℝ) (h : S.patch.Branches S.kernel G) (U : Config G f) (x : Site c) (w : Walk) :
    ‖(∫ V, S.density b U V • L (G.mat (travel V x w)) ∂prior G c) -
      ∑ z, S.likelihood U z • L (G.mat (travel (S.prediction U z) x w))‖ ≤
      K * (w.length:ℝ)^2 * (G.repDim:ℝ) * WilsonLinkEnergy.energy S G b := by
  letI : IsFiniteMeasureOnCompacts (prior G c) := inferInstanceAs
    (IsFiniteMeasureOnCompacts (Measure.pi (fun _ : Edge (Site c) => G.probHaar)))
  let M (V : Config G c) := L (G.mat (travel V x w))
  have hc : Continuous M := L.continuous.comp (G.continuous_mat.comp (continuous_travel w x))
  have hi z : Integrable (fun V => S.likelihood U z • (S.noise b (S.prediction U z) V • M V)) (prior G c) :=
    (continuous_const.smul ((noise_cont S b (S.prediction U z)).smul hc)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change ‖(∫ V, (∑ z, S.likelihood U z * S.noise b (S.prediction U z) V) • M V ∂prior G c) - _‖ ≤ _
  simp_rw [Finset.sum_smul,mul_smul]
  rw [integral_finsetSum _ (fun z _ => hi z)]
  simp_rw [integral_smul]
  rw [←Finset.sum_sub_distrib]
  simp_rw [←smul_sub]
  refine (norm_sum_le ..).trans ?_
  calc
    _ ≤ ∑ z, S.likelihood U z * (K*(w.length:ℝ)^2*(G.repDim:ℝ)*WilsonLinkEnergy.energy S G b) := by
      apply Finset.sum_le_sum
      intro z _
      rw [norm_smul, Real.norm_of_nonneg (S.likelihood_pos U z)]
      exact mul_le_mul_of_nonneg_left (conditional S L K hK hL b (S.prediction U z) x w) (S.likelihood_pos U z)
    _ = _ := by rw [←Finset.sum_mul,S.chosen h U,one_mul]

/-- One funded tail works for every cutoff, period, start, finite walk and
fine input; even the choice of walk may depend on the inherited level. -/
theorem selected (R : Run G) (hG : G.Simple) (L : G.Mat →L[ℝ] E) (K : ℝ) (hK : 0 ≤ K) (hL : ∀ X, ‖L X‖ ≤ K*‖X‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ m : ℕ in atTop, ∀ N p : ℕ, m < N →
      ∀ (x : Site (R.family.side m p)) (w : Walk) (U : Config G (R.family.side (m+1) p)),
      let S := R.family.path.levels.clock.op m p
      let β := R.family.path.β N p (m+1)
      ‖(∫ V, S.density β U V • L (G.mat (travel V x w)) ∂prior G _) -
        ∑ z, S.likelihood U z • L (G.mat (travel (S.prediction U z) x w))‖ ≤
        C*(w.length:ℝ)^2*(regulatorRun R.family N p (m+1))^2 := by
  obtain ⟨P,hP,H⟩ := WilsonLinkEnergy.calendar R.family.path.levels.clock
  refine ⟨K*(G.repDim:ℝ)*P,mul_nonneg (mul_nonneg hK (Nat.cast_nonneg _)) hP,?_⟩
  filter_upwards [WilsonPhysicalKernelClock.transport R hG H] with m hm N p hN x w U
  have he := hm N p hN m p
  rw [WilsonPhysicalKernelClock.temperature R N p (m+1) (Nat.succ_le_of_lt hN)] at he
  have h := mixture (R.family.path.levels.clock.op m p) L K hK hL (R.family.path.β N p (m+1))
    (R.family.path.levels.blocks m p).branches U x w
  exact h.trans ((mul_le_mul_of_nonneg_left he (mul_nonneg (mul_nonneg (hK) (sq_nonneg _)) (Nat.cast_nonneg _))).trans_eq (by ring))

end YM.Integration.WilsonWalkMatrixBias
end
