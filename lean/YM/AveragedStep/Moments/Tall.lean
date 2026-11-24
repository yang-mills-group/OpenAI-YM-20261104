import YM.AveragedStep.Moments.Winds
import YM.AveragedStep.Stokes.Fold
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Filter Function Lattice Wilson RG Tree Loops
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S:StepData c f} (F:Forest S.ratio)
def tall (τ:ℝ)(x:Site c)(e:Edge (Site f)):Query S G:=fun _ z=>τ*G.chord (Loops.stamped S F x z.1 z.2 e)
lemma tall_safe {x τ e}:Admits (tall (S:=S) (G:=G) F τ x e):=fun _=>env_continuous (by
  unfold tall; apply Continuous.mul continuous_const
  exact G.continuous_chord.comp ((continuous_apply e).comp (stamp_cont S F x)))
omit F in
-- exponent in fine distance from embedded reporting root
lemma tall_price (G:Gauge)(P:Patch)(K:KernelChoices)(h:P.Branches K G)(a:ℝ)(ha:0<a)(k:ℕ):
    ∃ C:ℝ,0≤C∧∀ᶠ τ:ℝ in atTop,∀ {c f:Side}(S:StepData c f)(F:Forest S.ratio),S.patch=P→ S.kernel=K→4∣f.val → (Real.log τ)^2 ≤ (c.val:ℝ)→20*P.L.val+20<f.val→∀ (x:Site c)(e:Edge (Site f)),Ranked τ (tall (G:=G) F τ x e) k (C*lag τ^k*plume a (S.ratio.embed x) e.1):=by
 by_cases hk:k=0
 · subst k; refine ⟨1,zero_le_one,Eventually.of_forall ?_⟩; intro τ c f S F hS hK _ _ _ x e
   exact (Ranked.zero (by rw [hS,hK]; exact h:S.patch.Branches S.kernel G) (tall_safe _)).enlarge (by simpa using plume_ge ha.le (S.ratio.embed x) e.1)
 obtain ⟨D,hD,m,H⟩:=Loops.stamp_price h
 obtain ⟨B,hB,W⟩:=breeze_paid G P K h k a ha
 obtain ⟨M,hM,L⟩:=face_paid G k
 obtain ⟨N,hN,T⟩:=noise_paid G K k
 let Z:ℝ:=D^k*((m:ℝ)^k*(m*M))
 have hZ:0≤Z:=by unfold Z; positivity
 let C:=2^k*(Z+2^k*(B*Real.exp a+N))
 refine ⟨C,by unfold C; positivity,?_⟩
 filter_upwards [W,T,eventually_ge_atTop (1:ℝ)] with τ HW HT ht
 intro c f S F hS hK he hg hj x e
 let i:Edge (Site c):=(S.ratio.parent e.1,e.2)
 obtain ⟨l,hl,hL⟩:=H c f S F hS hK hj e
 have hs:S.patch.Branches S.kernel G:=by rw [hS,hK]; exact h
 have hy(p):Ranked τ (scaledFace G S τ p) k (M*lag τ^k):=by
    refine ⟨face_admits G S τ p,?_⟩; simp_rw [abs_of_nonneg (scaledFace_pos _ _ (zero_le_one.trans ht) _ _ _)]
    exact L τ ht c f S hs he p
 let X:Query S G:= fun k u=> (l.map fun p=>scaledFace G S τ p k u).sum
 let q:=D • X + (breeze S τ x i + scaledNoise S τ i)
 have hR:Ranked τ (scaledNoise (G:=G) S τ i) k N := by
    refine ⟨noise_admits S τ i hs,?_⟩; simp_rw [abs_of_nonneg (scaledNoise_pos S (zero_le_one.trans ht) _ _ (_:Board G c f))]
    exact HT S hK hs i
 refine Ranked.enlarge (Ranked.below hs (q:=q) (tall_safe _) (ranked_plus hs hk ((ranked_list hs hk l _ _ hy).scale D)
     (ranked_plus hs hk (HW S hS hK he hg x i) hR)) ?_) ?_
 · intro j u _
   apply le_trans _ (le_abs_self _)
   change |τ*G.chord _| ≤ D * X j u + (τ* G.chord _ + τ*G.chord _)
   rw [abs_of_nonneg (mul_nonneg (zero_le_one.trans ht) (G.chord_nonneg _))]
   apply (mul_le_mul_of_nonneg_left (hL x u.1 u.2 j) (zero_le_one.trans ht)).trans_eq
   simp_rw [mul_add,mul_left_comm τ D,scaled_bill]; dsimp only [X,i,scaledFace]; rw [add_assoc]
 let A:=lag τ^k
 have hA:1≤ A:=one_le_pow₀ (lag_ge ht)
 let p:=plume a (S.ratio.embed x) e.1
 let b:=plume a x i.1
 have hp:1≤p:=plume_ge ha.le ..
 have hb:b ≤ Real.exp a*p := by
    unfold b p plume; rw [←Real.exp_add,show a+a*(separation (S.ratio.embed x) e.1:ℝ)=a*((separation (S.ratio.embed x) e.1:ℝ)+1) by ring]
    apply Real.exp_monotone; gcongr
    have he:= Work.E04.parent_separation S.ratio (S.ratio.embed x) e.1; rw [S.ratio.embed_parent] at he
    exact_mod_cast he
 have hl': (l.length:ℝ) ≤ m:=by exact_mod_cast hl
 change 2^k*(|D|^k*((l.length:ℝ)^k*(l.length*(M*A)))+2^k*(B*A*b+N))≤ C*A*p
 rw [abs_of_nonneg hD]; have hr: (l.length:ℝ)^k ≤ (m:ℝ)^k:= by gcongr
 calc
   _ ≤ 2^k*(D^k*((m:ℝ)^k*(m*(M*A)))+2^k*(B*A*(Real.exp a*p)+N)) := by
     have hA':0≤A:=zero_le_one.trans hA; gcongr
   _ = 2^k*(Z*A+2^k*(B*A*(Real.exp a*p)+N)) := by unfold Z; ring
   _ ≤ 2^k*(Z*A*p+2^k*(B*A*(Real.exp a*p)+N*A*p)):=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add (le_mul_of_one_le_right (mul_nonneg hZ (by linarith)) hp) (mul_le_mul_of_nonneg_left _ (by positivity))
      exact add_le_add_right ((le_mul_of_one_le_right hN hA).trans (le_mul_of_one_le_right (mul_nonneg hN (by linarith)) hp)) _
   _ = _:=by unfold C; ring

omit F in
lemma fine_breeze (G:Gauge)(P:Patch)(K:KernelChoices)(h:P.Branches K G)(a:ℝ)(ha:0<a)(k:ℕ):
    ∃ C:ℝ,0≤C∧∀ᶠ τ:ℝ in atTop,∀ {c f:Side}(S:StepData c f),S.patch=P→ S.kernel=K→4∣f.val → (Real.log τ)^2 ≤ (c.val:ℝ)→∀ (x:Site c)(i:Edge (Site c)),Ranked τ (breeze (G:=G) S τ x i) k (C*lag τ^k*plume a (S.ratio.embed x) (S.ratio.embed i.1)):=by
 obtain ⟨C,hC,H⟩:=breeze_paid G P K h k a ha
 refine ⟨C*Real.exp a,by positivity,?_⟩
 filter_upwards [H,eventually_ge_atTop (1:ℝ)] with τ H ht c f S hS hK hf hV x i
 have he:= Work.E04.parent_separation S.ratio (S.ratio.embed x) (S.ratio.embed i.1)
 rw [S.ratio.embed_parent,S.ratio.embed_parent] at he
 have hb:plume a x i.1 ≤ plume a (S.ratio.embed x) (S.ratio.embed i.1) * Real.exp a:=by
   unfold plume; rw [←Real.exp_add,show a * (separation (S.ratio.embed x) (S.ratio.embed i.1):ℝ) + a=a*((separation _ _:ℝ)+1) by ring]
   apply Real.exp_monotone; gcongr; exact_mod_cast he
 exact (H S hS hK hf hV x i).enlarge ((mul_le_mul_of_nonneg_left hb
    (mul_nonneg hC (pow_nonneg (zero_le_one.trans (lag_ge ht)) _))).trans_eq (by ring))
end YM.AveragedStep
