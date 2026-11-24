import YM.Contacts.Shuttle.Fairway
/-! # Carve moments of this charge cloud -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
noncomputable section
namespace YM.Contacts.Shuttle.Tide
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix
open MeasureTheory Labels Source Drops Analysis Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Pulse Spine Origin
open Milling Milling.Steam Milling.Forge Milling.Garf Tensor MultiNext.SignedSource Pattern Broadcast
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{X Y ι κ Z E : Type}[Fintype ι][NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{s:ℝ≥0}{b c:ℝ}{h k n:ℕ}
private abbrev S (x: Cover) :ℝ:= 1+size x
theorem shadeGlow (u:Stack E h)(x y: Cover)(he:size y ≤ size x) : ‖glow E h u (xyz y)‖ ≤ ((h:ℝ)+1)*‖u‖*S x ^h := by
   have hs : 1≤ S x := le_add_of_nonneg_right (Nat.cast_nonneg _); have hw : ‖xyz y‖ ≤ S x:= (Planned.PrimaryIntegral295.Carrier.shade_seat y).trans ((show (size y:ℝ)≤ size x by exact_mod_cast he).trans (le_add_of_nonneg_left zero_le_one)); rw [shining]; apply (norm_sum_le ..).trans; refine (Finset.sum_le_sum (g:=fun i:Fin (h+1)=> ‖u‖*S x^h) ?_).trans_eq ?_; swap; · simp [mul_assoc]
   intro i _; apply ((u i).le_opNorm ..).trans; simp only [prod_const,card_univ,Fintype.card_fin]; exact mul_le_mul (norm_le_pi_norm u i) ((pow_le_pow_left₀ (norm_nonneg _) hw _).trans (pow_le_pow_right₀ hs (by omega))) (by positivity) (norm_nonneg _)
lemma lung {p:E4→E}(h:p∈ Powers.space E4 E k) : ∃ c:ℝ,0≤c ∧ ∀ x y: Cover, size y ≤ size x → ‖p (xyz y)‖ ≤ c*S x^k:= by
   refine ⟨_, mul_nonneg (b:=‖fit k p‖) (a:=(k:ℝ)+1) (by positivity) (norm_nonneg _),fun x y hh=>?_ ⟩; have he:= shadeGlow (fit k p) _ _ hh; rwa [sky h] at he
local notation "N" => Node (Dyes G)
local notation "m⊎" x => axisEquiv.symm ((x).2.1)
def lens (G:Gauge) (k:ℕ)(x:Node (Dyes G)) : Ship G k →L[ℝ] ℝ:= (EuclideanSpace.proj x.2.2).comp ((glance G.Color k (xyz x.1)).comp (ContinuousLinearMap.proj (m⊎x)))
lemma glaze (G:Gauge) (k:ℕ): Ice (Tide.lens G k) (fun x=> blast x^k) (k+1):= by
   intro x; let f:ℝ:=k+1; refine ContinuousLinearMap.opNorm_le_bound _ (by unfold blast; positivity) (fun y=>?_); change ‖glow G.Color k (y _) (xyz x.1) (x.2.2)‖ ≤ _; refine (PiLp.norm_apply_le ..).trans ((shadeGlow (y (m⊎x)) x.1 x.1 le_rfl).trans (?_ )); refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_le_pi_norm y (m⊎x)) (by positivity)) (by unfold S; positivity)) ?_; change f*‖y‖* blast x^k≤f*_ *‖y‖; rw [mul_right_comm]
lemma glaze_at (x:Cover)(i:Axis)(v:G.ColorIndex)(y:Ship G k): lens G k (x,coord i,v) y=glow G.Color k (y i) (xyz x) v:= by
   change _= _; unfold lens; simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]; change EuclideanSpace.proj (𝕜:=ℝ) v (glance _ _ _ (y (axisEquiv.symm (axisEquiv i))))= _; rw [axisEquiv.symm_apply_apply]; rfl
lemma needTurn (k i:ℕ)(v : Draft G h)(a:Axis) : ∃ c:ℝ, 0≤c ∧ ∀ m:Side,∀ x: Cover, ‖timber m (wrap m x) a v‖ ≤ c*S x^h:= by
   let h1:= spot (E:=G.Color) v.1; let p:=place v; obtain ⟨b,hb,hB⟩:= lung h1; obtain ⟨c,hc,hC⟩:= lung (k:=h) (Powers.widen (h-1) _ (by omega) (coats a v.2 h (fun i hi=> by omega))); change ∀ x y:Cover,size y ≤ size x → ‖p (xyz y)‖ ≤ _ at hB
   have hf m (x:Cover) : ‖p (xyz (lift (wrap m x)))‖ ≤ b * S x^h:= hB x _ (FreeResolvent.wrap_size ..)
   refine ⟨c+b*2^h+b,by positivity,fun m x=>?_ ⟩; let y:= wrap m x; let y':= y+Lattice.step a; rw [timber_form (G:=G) m v (y,a)]; change max ‖p (xyz (lift y))‖ (max ‖p (xyz (lift y'))-p (xyz (lift y))‖ ‖tempo (d:=h) (xyz (lift y)) a v.2‖)≤ _; have he:= hf m x; have hl : ‖tempo (d:=h) (xyz (lift y)) a v.2‖ ≤ c * S x^h:= hC x _ (FreeResolvent.wrap_size ..)
   have hy: ‖p (xyz (lift y'))‖ ≤ b*2^h*S x^h:= calc
      _ ≤ b*S (x+Lattice.step a)^h:= by rw [show y'=wrap m (x+Lattice.step a) from (by rw [map_add,Lattice.wrap_step])]; exact hf m _
      _ ≤ b*(2*S x)^h:= by
           have hr : S (x+Lattice.step a) ≤ 2*S x:= by
               have hb : (size (x+Lattice.step a):ℝ) ≤ size x + (1:ℝ):= by exact_mod_cast ((size_add x (Lattice.step a)).trans (Nat.add_le_add_left (by simp [Laurent.size,apply_ite Int.natAbs]) (size x)))
               unfold S; linarith only [hb, Nat.cast_nonneg (α:=ℝ) (size x)]
           exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by unfold S; positivity) hr h) hb
      _ = _ := by rw [mul_pow,mul_assoc]
   change ‖p (xyz (lift y))‖ ≤ _ at he; have ht : 0≤ S x^h:= by unfold S; positivity
   rw [add_mul,add_mul]; refine max_le ((he).trans (le_add_of_nonneg_left (by positivity))) (max_le ((norm_sub_le ..).trans (add_le_add (hy.trans (le_add_of_nonneg_left (mul_nonneg hc ht))) he)) ((hl).trans ((le_add_of_nonneg_right (mul_nonneg (mul_nonneg hb (pow_nonneg zero_le_two _)) ht)).trans (le_add_of_nonneg_right (mul_nonneg hb ht)))))
lemma needs (k:ℕ) (v : Fin k→ Draft G h)(H:Hol G): ∃ c≥(0:ℝ), ∀ m:Side, Ice (fun x:N=> iteratedFDeriv ℝ k (north H m) 0 v (lower m x)) (fun x=> blast x^(k*h)) c:= by
   choose b hb hB using fun i:Fin k=>fun a:Axis=> needTurn 0 0 (v i) a; let f a:=‖iteratedFDeriv ℝ k (stereo G h) 0‖*∏ i,b i a; have hf a : 0≤ f a:= mul_nonneg (norm_nonneg (iteratedFDeriv ℝ k (stereo G h) 0)) (prod_nonneg fun i _=> hb i a)
   refine ⟨∑ i:Axis, f i,sum_nonneg (fun i _=>hf i),fun m x=>?_⟩
   rcases x with ⟨x,a,z⟩; obtain ⟨a,rfl⟩:= axisEquiv.surjective a; change ‖iteratedFDeriv ℝ k (north H m) 0 v (_,coord a,z)‖ ≤ _* S x ^_; rw [north_turn]; refine (PiLp.norm_apply_le ..).trans (((iteratedFDeriv ℝ k (stereo G h) 0).le_opNorm _).trans ?_)
   apply le_trans (mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _=> norm_nonneg _) (fun i _=> hB i a m x)) (norm_nonneg _)); simp_rw [prod_mul_distrib,prod_const, card_univ,Fintype.card_fin, ←pow_mul,← mul_assoc, mul_comm h]; exact mul_le_mul_of_nonneg_right (single_le_sum (f:=f) (fun i _=> hf _) (mem_univ _)) (by unfold S; positivity)
end YM.Contacts.Shuttle.Tide
