import YM.WilsonCoeffUV.Step.Stencils

/-! The same prediction and probability even with unused tag slots. Frame
normalization is NOT repeated once per log variable. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV
open Wilson Lattice Laurent Exterior Bloch Matrix Precision Stationary RG Blue
open Next.Free FreeResolvent Tree Filter Gauge Metric Function
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {c f : Side}

section moments
variable {X: Type} [Fintype X] {b:Lawn X→ℝ} {K:Matrix X X ℝ}
lemma sprouts_move (hz:b 0=0)(he:fderiv ℝ b 0=0) : PowerSeries.X^2 * flash (sprig b 2)=jet b := by
  refine moves b fun i hi=>?_ ; interval_cases i
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,jet_lead,hz,map_zero]
  rw [jet_apply];
  rw [show rye b 1=0 from funext fun s=> by unfold rye; rw [iteratedFDeriv_one_apply,he]; simp, map_zero]
lemma sprouts_lead (h:Green b)(he:∀ i j, iteratedFDeriv ℝ 2 b 0 ![i,j]=dotProduct i (K*ᵥ j)) (hK:K.transpose=K) :
    sprig b 2 0=shine (orbQ K) := by
  apply congrArg (Blue.shine (k:=2)); apply unique_kernel (rye_sym h 2) (orb_smooth K hK); apply MvPolynomial.funext; intro x
  rw [orb_eval,←jet_apply,rayon,show (fun _:Fin 2=>x)= ![x,x] from funext (fun i=>by fin_cases i <;> rfl),he,smul_eq_mul]; norm_num [Nat.factorial]; ring
end moments
section tags
variable (S:StepData c f)
lemma penalty_same (h:S.patch.Branches S.kernel G) : ∀ᶠ x : TreeVars G f in 𝓝 0, ∀ k:S.Choices, S.prediction (mantle x) k=S.prediction (mantle x) (tac S) := by
  let T := (cloth G f).symm
  have ht: Tendsto T (𝓝 0) (𝓝 0) := by simpa using (T.continuous.tendsto 0)
  apply eventually_all.mpr; intro k
  filter_upwards [ht.eventually (eventually_all.mpr (Push.lips S h · k)), ht.eventually (eventually_all.mpr (Push.lips S h · (tac S))), ht.eventually (eventually_all.mpr (Push.threshold S ·))] with x ha hb he
  funext i
  rw [mantle, ha i,hb i]
  apply congrArg G.focus
  have hh t b : S.frames (mantle x) t b = S.frames (mantle x) (tac S).1 b:= by
    unfold StepData.frames
    rw [Patch.frame,Patch.frame,if_pos,if_pos]; exacts [he _,he _]
  unfold Push.bonds Push.deck StepData.connector; simp_rw [show represent (T x)=mantle x from rfl, hh k.1]

lemma exact_density (V: Config G c) (β:ℝ) (h:S.patch.Branches S.kernel G) : ∀ᶠ x:TreeVars G f in 𝓝 0,
    S.density β (mantle x) V=S.noise β (S.prediction (mantle x) (tac S)) V := by
  filter_upwards [penalty_same S h] with x hx
  unfold StepData.density; simp_rw [hx,← Finset.sum_mul,S.chosen h,one_mul]
lemma noise_toll (V : Config G c) (U :Config G f) (b:ℝ)(k):
    S.noise b (S.prediction U k) V=(S.penaltyZ b G)⁻¹ ^ (Fintype.card (Edge (Site c))) * Real.exp (-b*noiseTaylor S V U k) := by
  rw [noiseTaylor,← mul_assoc,Finset.mul_sum, Real.exp_sum,StepData.noise, Finset.prod_mul_distrib]; simp [StepData.penaltyWeight]

/-- usable without computing pointwise derivative of a mask -/
theorem entire_shared (h:S.patch.Branches S.kernel G): ∀ᶠ x:TreeVars G f in 𝓝 0,
     ∀ (V: Config G c)(β:ℝ), S.density β (mantle x) V=(S.penaltyZ β G)⁻¹ ^ (Fintype.card (Edge (Site c)))*Real.exp (-β*noiseTaylor S V (mantle x) (tac S)) := by
  filter_upwards [penalty_same S h] with x hx V β
  rw [← noise_toll]; unfold StepData.density; simp_rw [hx,← Finset.sum_mul,S.chosen h,one_mul]

lemma price_channel (h:S.patch.Branches S.kernel G)(A A':Lawn (Joint G f c))(s:Signed)(b:Site c)(g:Site f→G.El)
    (he : mantle (leftArm A')=Lattice.gauge g (pull s (S.ratio.embed b) (mantle (leftArm A))))
    (hy : mantle (rightArm A')=Lattice.gauge (g ∘ S.ratio.embed) (pull s b (mantle (rightArm A))))
    (hf :∀ k,S.prediction (mantle (leftArm A)) k=S.prediction (mantle (leftArm A)) (tac S))
    (ht :∀ k,S.prediction (mantle (leftArm A')) k=S.prediction (mantle (leftArm A')) (tac S)): jointPen G S A=jointPen G S A' := by
  have hw : S.density 1 (mantle (leftArm A')) (mantle (rightArm A')) = S.density 1 (mantle (leftArm A)) (mantle (rightArm A)) := by rw [he,hy, S.covary h,S.channel h]
  unfold StepData.density at hw; simp_rw [ht,hf,← Finset.sum_mul, S.chosen h,one_mul,noise_toll] at hw
  have hZ : (S.penaltyZ 1 G)⁻¹ ≠ 0 := (inv_pos.mpr (S.penaltyZ_pos _)).ne'
  have hw := Real.exp_injective (mul_left_cancel₀ (pow_ne_zero _ hZ) hw.symm)
  unfold jointPen; linarith only [hw]
end tags
end YM.WilsonCoeffUV
