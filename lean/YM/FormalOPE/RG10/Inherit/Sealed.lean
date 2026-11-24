import YM.FormalOPE.RG10.Inherit.Credential
/-!
 # Adding a price to accounts. For reference Gaussian coordinates.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Inherit
open Function Filter Topology MeasureTheory PertExtension Series Precision
open BlockGauge Series.Radial Push.Loops Chart
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
lemma plus (k:ℕ) {a b:E→ℝ} (ha:ContDiffAt ℝ ω a 0)(hb:ContDiffAt ℝ ω b 0)(u): jet (a+b) k u=jet a k u+jet b k u:=by
 unfold jet; rw [iteratedFDeriv_add_apply (ha.of_le le_top) (hb.of_le le_top)]; exact mul_add .. -- after Map.add_apply?
lemma times (k:ℕ) (s:ℝ) {a:E→ℝ}(ha:ContDiffAt ℝ ω a 0)(u:E): jet (s • a) k u=s*jet a k u:= by
 unfold jet; rw [iteratedFDeriv_const_smul_apply (ha.of_le le_top)]; simp only [smul_apply,smul_eq_mul]; ring
variable {G : Gauge}{I J : Type}[Fintype I][Fintype J]
structure Strong (a:Spending G I): Prop extends Credential a where
 cont:Continuous a
 pos (u): u≠1 →0<a u
-- use to prove reference positivity easily
namespace Strong
variable {a:Spending G I}{b:Spending G J}
lemma grant (a:Spending G I)(center:a 1=0)(positive:∀ u,u≠1→0<a u)(ha:Continuous a) (h:ContDiffAt ℝ ω (a ∘ expLinks G I) 0)
 (g:∀ u,u≠0→ 0<jet (a ∘ expLinks G I) 2 u):Strong a where
 meas:=ha.measurable
 nn u:= by by_cases hu:u=1
           · rw [hu,center]
           exact (positive u hu).le
 center:=center
 smooth:=h
 strict:=g
 cut := compactAid ha positive
 cont:=ha
 pos := positive
lemma tune (A:Strong a) {s:ℝ}(hs:0<s): Strong (s • a):= grant _
 (by simp [A.center]) (fun u hu=> mul_pos hs (A.pos u hu))
 (A.cont.const_smul _) (contDiffAt_const.smul A.smooth)
 (fun u hu=> by change 0<jet (s • (a ∘ expLinks G I)) _ _; rw [times _ _ A.smooth]; exact mul_pos hs (A.strict u hu))
lemma soft (A:Strong a)(x:Direction G I):0 ≤ jet (a ∘ expLinks G I) 2 x:= by
 by_cases hx : x=0
 · subst x; unfold jet; rw [iteratedFDeriv_two_apply]; simp
 exact (A.strict x hx).le
omit [Fintype I] [Fintype J] in
lemma onePart {E:Type}{x y:I⊕J→ E} (h:x≠y): x ∘ Sum.inl ≠ y ∘ Sum.inl ∨ x ∘ Sum.inr ≠ y ∘ Sum.inr:= by
 by_contra! H; exact h (funext fun i=> by cases i with
                                           | inl i => exact congr_fun H.1 i
                                           | inr i=>exact congr_fun H.2 i)
-- generic free reindex
 def wave (f:I→J): Direction G J →L[ℝ] Direction G I:= ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj (f i)
variable (f:I→J)
lemma view (B: Component a): Component (fun u: Configuration G J=> a (u∘ f)) where
 meas:= by let p:=fun u:Configuration G J=> u∘f; exact B.meas.comp (f:=p) (measurable_pi_lambda _ (fun i=> measurable_pi_apply (f i))) -- syntax
 nn x:= B.nn _
 center:= B.center
 smooth:= (show ContDiffAt ℝ ω _ ((wave (G:=G) f) 0) from by rw [map_zero]; exact B.smooth).comp _ ((wave (G:=G) f).contDiff.contDiffAt) -- API?
lemma withSecond (B:Component a) (u:Direction G J) : jet ((fun (w:Configuration G J)=> a (w∘f)) ∘ expLinks G J) 2 u=jet (a ∘ expLinks G I) 2 (u ∘ f):= by
 have he:= second (k:=wave (G:=G) f) (wave (G:=G) f).contDiff.contDiffAt (map_zero _) B.smooth ?_ u
 · change jet ((a ∘ expLinks G I) ∘ (wave (G:=G) f)) 2 u=_
   rw [he, ContinuousLinearMap.fderiv]; rfl
 exact (show IsLocalMin (a ∘ expLinks G I) 0 from Filter.Eventually.of_forall (fun x=> by change a (expLinks G I 0) ≤ _; rw [identity_zero,B.center]; exact B.nn _ )).fderiv_eq_zero
 def united (a:Spending G I)(b:Spending G J)(u:Configuration G (I⊕ J)) := a (u ∘ Sum.inl) + b (u ∘ Sum.inr)
lemma merge (A:Strong a) (B:Strong b) : Strong (united a b):=grant _
 (by change a 1 + b 1=0; simp [A.center,B.center])
 (fun u hu=> (onePart hu).elim (fun h=> add_pos_of_pos_of_nonneg (A.pos _ h) (B.nn _)) (fun h=> add_pos_of_nonneg_of_pos (A.nn _) (B.pos _ h)))
 (by
   unfold united; exact (A.cont.comp (continuous_pi (f:=fun x:Configuration G (I⊕J)=> x ∘ Sum.inl) (fun _=>continuous_apply _))).add (B.cont.comp (continuous_pi (f:=fun x:Configuration G (I⊕J)=> x ∘ Sum.inr) (fun _=>continuous_apply _))))
 ((view (J:= I⊕J) Sum.inl A.toComponent).smooth.add (view (J:= I⊕J) Sum.inr B.toComponent).smooth)
 (fun u hu=> by
  have H:= plus 2 (view Sum.inl A.toComponent).smooth (view Sum.inr B.toComponent).smooth u
  rw [withSecond Sum.inl A.toComponent, withSecond Sum.inr B.toComponent] at H
  rw [show jet (united a b ∘ expLinks G (I⊕J)) 2 u = jet _ _ _ + jet _ _ _ from H]
  rcases onePart hu with h|h
  · exact add_pos_of_pos_of_nonneg (A.strict _ h) (B.soft _)
  exact add_pos_of_nonneg_of_pos (A.soft _) (B.strict _ h))
end Strong
end YM.FormalOPE.RG10.Inherit
