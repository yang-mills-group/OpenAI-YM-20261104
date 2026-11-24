import YM.MS.ScaleForest.JointScale
/-!
# Test the ghost-bubble contribution at multiple placements

Keep the Feynman integrals vs Laurent representatives distinct. Log scale
change carries the upper length at every step. Can also use the result at
removed IR length, justified by `Frontier`. Gives pointwise distribution
reads on the open position stratum ONLY. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Triangle
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum Tone Detect Osc Fiddle XSpace XSpace.Chiral Cylinder Planted Quadratic
open scoped Topology ContDiff
variable {G : Gauge} {I : Type} (μ : ℝ) (X Y : Pupil) (A:I→QP) (u:ℝ) (V:GraphSum G true 4)

-- symbols with Wstar units. Scalar values in [] slots are also absolute.
def D (G:Gauge) := nominal μ (triangle X Y A (vertex (ghostR G)))
def H (G:Gauge) := nominal μ (triangle X Y A (ghostV G))
def BareG (G:Gauge) := lineIntegral μ X Y A (ghostV G).instructions.prep
-- use dimensional argument z, remember z=-ε
lemma eps_pay (G:Gauge)(e:ℂ): (proton 1 (D μ X Y A G)) (-e)= -(e⁻¹ • (D μ X Y A G) (-e)) := by rw [proton,pow_one,inv_neg,neg_smul]

section
variable [TopologicalSpace I] [FirstCountableTopology I] (hA:AdmittedGap A)
include hA
omit [FirstCountableTopology I] in
lemma admittedSurge : AdmittedGap (surge A u):= by
   obtain ⟨hV,⟨C,hC,hE⟩,⟨D,hD,hℓ⟩⟩:= hA
   refine ⟨ hV.const_smul (exp u), ⟨ exp u * C,by positivity,?_⟩,⟨ exp u* D,by positivity,?_⟩ ⟩ <;> first| ( intro x; unfold surge; rw [norm_smul,Real.norm_of_nonneg (by positivity)]; gcongr; first|exact hE _|exact hℓ _)

lemma Bare_era (G:Gauge): OrbitNorm u (BareG μ X Y A G) (BareG μ X Y (surge A u) G) (fun z=> -8-6*z) := by
   have H:=initial_era μ X Y A u hA (boarded (ghostV G) rfl) (show monoPage 1 _ from ⟨ _,in_page1 ⟩); norm_num at H; exact H
lemma D_era (G:Gauge): OrbitNorm u (D μ X Y A G) (D μ X Y (surge A u) G) (fun z=> -8-4*z) := by
   have h:= initial_era μ X Y A u hA (roll (ghostR G) rfl) (ℓ:=0) ⟨ _,renorm_vertex _ ⟩; rw [ Nat.cast_zero,mul_zero,add_zero ] at h
   exact OrbitNorm.congr u h (EventuallyEq.symm (accounted μ X Y A _ rfl)) (EventuallyEq.symm (accounted μ X Y _ _ rfl))

variable {m : ℕ} (w : Legs (Shore G m)) (s:ℝ)(x:I)
private abbrev Dval (V:Planted.Plan G I true)(z:ℂ)(s:ℝ) := nominal μ V z s x m w
private theorem arrives (G:Gauge) : Frontier (H μ X Y A G) ∧ Frontier (D μ X Y A G):= ⟨ (abide μ _ (hiredFamily _ _ _ _ hA)).2.1,(abide μ _ (hiredFamily _ _ _ _ hA)).2.1⟩
local notation "𝔣" => D μ X Y A G
local notation "𝔥" => H μ X Y A G
lemma priceJet : DifferentiableAt ℂ (fun z=> D μ X Y A G z s x m w) 0 ∧ DifferentiableAt ℂ (fun z=> H μ X Y A G z s x m w) 0:= by
   have ht (W:GraphSum G true 4): DifferentiableAt ℂ (fun z=> Dval μ w x (triangle X Y A W) z s) 0 := by obtain ⟨R,hR,hT⟩:= (abide μ _ (hiredFamily X Y A W hA)).1; exact (hT s x).top _ _ 0 hR.top
   exact ⟨ht _,ht _⟩

-- check mistake of first dropping z-dependence of the contracted outside
-- scales. Even on arbitrary projected tensor components.
theorem premature : let d(z:ℂ):=D μ X Y A G z s x m w; Tendsto (fun z=> z⁻¹*(d z-d 0)) dotty (𝓝 (deriv d 0)) ∧
    Tendsto (fun z=> BareG μ X Y A G z s x m w + z⁻¹*d 0) dotty (𝓝 (H μ X Y A G 0 s x m w-deriv d 0)):= by
   intro d; obtain ⟨he,hP⟩:= priceJet μ X Y A hA w s x; have hx := he.hasDerivAt.tendsto_slope; have h : Tendsto (fun z=>z⁻¹*(d z-d 0)) dotty (𝓝 (deriv d 0)):= by simpa only [slope_fun_def_field,sub_zero,div_eq_mul_inv,mul_comm] using! hx
   refine ⟨ h,(hP.continuousAt.continuousWithinAt.tendsto (s:= {0}ᶜ) |>.sub h).congr' ?_⟩
   filter_upwards [ghost_input (G:=G) μ X Y A hA] with z hz; obtain he := congr_fun (congr_fun (congr_fun (congr_fun hz s) x) m) w
   change H μ X Y A G z s x m w = BareG μ X Y A G z s x m w + z⁻¹^1 * d z at he; rw [he]; ring

def α (u:ℝ)(z:ℂ):= amount (-8-6*z) u
def β (u:ℝ)(z:ℂ):= amount (-8-4*z) u
lemma z_surge : ∀ᶠ z in dotty, H μ X Y (surge A u) G z = fun s=> α u z • H μ X Y A G z (s-u) +
    (z⁻¹*(β u z-α u z)) • D μ X Y A G z (s-u):= by
   filter_upwards [ Bare_era μ X Y A u hA G, D_era μ X Y A u hA G, ghost_input μ X Y A hA (G:=G), ghost_input μ X Y _ (admittedSurge A u hA) (G:=G) ] with z hB hD hH ht;
   funext s; let a:=surge A u;
   change H μ X Y a G z s= _; change H μ X Y A G z = _ at hH; rw [show H μ X Y a G z = BareG μ X Y a G z + z⁻¹^1 • D μ X Y a G z from ht ];
   have hz (F Y:Curtain G I) (c:ℂ)(h:timing u Y z=c • F z) : Y z s = c • F z (s-u) := by obtain hp:= congr_fun h (s-u); simpa only [timing,sub_add_cancel,Pi.smul_apply] using hp
   change H μ X Y A G z = BareG μ X Y A G z + z⁻¹^1 • D μ X Y A G z at hH
   simp only [Pi.add_apply,Pi.smul_apply]; rw [ hz _ _ (α u z) hB, hz _ _ (β u z) hD , hH ]; simp only [ sub_smul, mul_sub,← mul_smul, Pi.add_apply,Pi.smul_apply, smul_add, pow_one ]; rw [ mul_comm (α u z) ]; abel

omit hA [TopologicalSpace I][FirstCountableTopology I] in
lemma amtD (a x z:ℂ): HasDerivAt (fun z:ℂ=> amount (a+x*z) u) (( u*x:ℂ) * amount (a+x*z) u) z:= by
   convert! (( ( (hasDerivAt_id' z).const_mul x ).const_add a ).const_mul (u:ℂ)).cexp using 1; unfold amount; ring
omit hA [TopologicalSpace I][FirstCountableTopology I] in
private lemma differ : Tendsto (fun z:ℂ=> z⁻¹*(β u z-α u z)) dotty (𝓝 (2*(u:ℂ)*amount (-8) u)):= by
   let W(z:ℂ):= β u z-α u z; have he : W 0=0:= by simp [W,β,α]
   have ht : HasDerivAt W (2*(u:ℂ)*amount (-8) u) 0:= by
      unfold W β α; convert ((amtD u (-8) (-4) 0).fun_sub (amtD u (-8) (-6) 0) ) using 1 <;> first| rfl| (solve| simp only [mul_zero,add_zero]; ring)| (ext1; simp [sub_eq_add_neg])
   have hp:= ht.tendsto_slope; simp_rw [slope_fun_def_field,he, sub_zero, div_eq_mul_inv] at hp; simpa only [W,mul_comm] using hp

lemma alarm_H : H μ X Y (surge A u) G 0 (s+u) x m w = amount (-8) u * (H μ X Y A G 0 s x m w + (2*(u:ℂ))* D μ X Y A G 0 s x m w) := by
   let a:=surge A u; obtain ⟨hZ,hH⟩:= priceJet μ X Y A hA w s x; obtain hx: Tendsto (α u) dotty (𝓝 (α u 0)):= (show Continuous (α u) from (by unfold α amount; fun_prop)).continuousAt.continuousWithinAt
   have hh:= tendsto_nhds_unique_of_eventuallyEq (l:=dotty) ((priceJet μ X Y a (admittedSurge A u hA) w (s+u) x).2.continuousAt.continuousWithinAt)
      ((hx.mul hH.continuousAt.continuousWithinAt).add ((differ u).mul hZ.continuousAt.continuousWithinAt)) ( (z_surge (G:=G) μ X Y A u hA).mono (fun z hz=> by simp only [a, hz, Pi.smul_apply,Pi.add_apply,add_sub_cancel_right,smul_eq_mul]) )
   dsimp only [a] at hh; rw [hh,α,mul_zero,sub_zero]; ring
lemma alarm_D : (fun z:ℂ=> D μ X Y (surge A u) G z (s+u) x m w)=ᶠ[𝓝 0] (fun z=> β u z*D μ X Y A G z s x m w):= by
   let f(z:ℂ):= 𝔣 z s x m w; let g(z:ℂ):= D μ X Y (surge A u) G z (s+u) x m w
   have hh: g=ᶠ[dotty] (fun z=>β u z*f z):= (D_era μ X Y A u hA G).mono (fun z hz=> congr_fun (congr_fun (congr_fun (congr_fun hz s) x) m) w)
   have he : g 0=β u 0*f 0:= tendsto_nhds_unique_of_eventuallyEq (l:=dotty) ((priceJet μ X Y _ (admittedSurge A u hA) w (s+u) x).1.continuousAt.continuousWithinAt) ((((show Continuous (β u) by unfold β amount; fun_prop).continuousAt).continuousWithinAt).mul ((priceJet μ X Y A hA w s x).1.continuousAt.continuousWithinAt)) hh
   obtain ⟨R,hR,hV⟩:= dotty_mem.mp hh; refine Metric.mem_nhds_iff.mpr ⟨ R,hR,fun z hz=>?_ ⟩; by_cases hp:z=0; subst z; exact he; exact hV z hz hp
lemma DScale : D μ X Y (surge A u) G 0 (s+u) x m w=amount (-8) u*D μ X Y A G 0 s x m w:= by obtain h:= (alarm_D μ X Y A u hA w s x).eq_of_nhds; simpa only [β,mul_zero,sub_zero] using h
-- slope of complement numerator itself changes additively
lemma DScaleJet : deriv (fun z:ℂ=> D μ X Y (surge A u) G z (s+u) x m w) 0=amount (-8) u * (deriv (fun z:ℂ=> D μ X Y A G z s x m w) 0 - 4*(u:ℂ)* D μ X Y A G 0 s x m w):= by
   rw [ (alarm_D μ X Y A u hA w s x).deriv_eq ]; obtain h : HasDerivAt (β u) (-4*(u:ℂ)*amount (-8) u) 0:= by unfold β; convert amtD u (-8) (-4) 0 using 1 <;> first| (ext; simp [sub_eq_add_neg]) | (simp; first| (solve| ring)| (ring_nf; simp))
   rw [ HasDerivAt.deriv ( HasDerivAt.fun_mul h (priceJet μ X Y A hA w s x).1.hasDerivAt) ]; unfold β; simp only [mul_zero,sub_zero]; ring

lemma limit_s (G:Gauge) (U:GraphSum G true 4) (x:I) : Tendsto (fun s=> nominal μ (triangle X Y A U) 0 s x 0 []) atTop (𝓝 (WindowIR (nominal μ (triangle X Y A U)) 0 0 x)):= by obtain ⟨R,hR,hF⟩:= (abide μ _ (hiredFamily X Y A U hA)).2.1 (1/2) (by norm_num) (by norm_num); exact (Frontier.enter hF (by norm_num) 0).2.2.2 0 hR.top x
lemma IR_s (G:Gauge) : WindowIR (H μ X Y (surge A u) G) 0 0 x = amount (-8) u*(WindowIR (H μ X Y A G) 0 0 x+(2*(u:ℂ))*WindowIR (D μ X Y A G) 0 0 x):= by
   have h:= (limit_s μ X Y _ (admittedSurge A u hA) G (ghostV G) x).comp (tendsto_atTop_add_const_right atTop u tendsto_id)
   refine tendsto_nhds_unique_of_eventuallyEq h (((limit_s μ X Y A hA G (ghostV G) x).add ((limit_s μ X Y A hA G (vertex (ghostR G)) x).const_mul (2*(u:ℂ)))).const_mul (amount (-8) u)) (Eventually.of_forall fun s=> alarm_H _ _ _ _ _ hA _ _ x)
end
end YM.MS.ScaleForest.Triangle
