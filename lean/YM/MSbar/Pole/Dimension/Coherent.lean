import YM.MSbar.Pole.Dimension.Transit

/-! # Generic tensor equality for dimensional integrations -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Ambient
open Set Function Filter MeasureTheory place Radial
open scoped Topology InnerProductSpace ContDiff Classical BigOperators Real
variable {I : Type} [Fintype I] {n : ℕ} {F : Screened I}
private def north (F : Screened I) (x : External I n) (y : place n) (z : ℝ × ℂ) :=
    lifting (n+1) F (z.1,portal n (y,z.2),pad n ∘ x)
omit [Fintype I] in
lemma linking (h : Texture F) (x : External I n) (y : place n) (s : ℝ):
    lifting n F (s,y,x)= north F x y (s,0) := by
  let U := portal (n+1) (portal n (y,(s:ℂ)),0); let V := portal (n+1) (portal n (y,0),(s:ℂ))
  have he : ‖U‖^2 = ‖V‖^2 := by simp [U,V,squared]
  obtain ⟨J,hJ,H⟩:=place.sphere he
  let X : External I (n+2):= pad (n+1) ∘ pad n ∘ x
  have hx : J ∘ X = X := funext fun i=> H _ (by simp [U,V,X])
  have ht := (h.moves (n+2) J U X).symm
  unfold north lifting; simp only; rw [← h.agrees]
  change F (n+2) (U,X)=F (n+2) (V,X); rwa [hJ,hx] at ht
omit [Fintype I] in
lemma north_round (h : Texture F) (x : External I n) (y : place n): Globular (north F x y) := by
  intro t s u v hh
  let U:=portal (n+1) (portal n (y,u),(t:ℂ)); let V:= portal (n+1) (portal n (y,v),(s:ℂ))
  have he : ‖U‖^2 = ‖V‖^2 := by unfold U V; simp [squared]; linarith
  obtain ⟨J,hJ,H⟩:=place.sphere he
  let X : External I (n+2):= pad (n+1) ∘ pad n ∘ x
  have hx : J ∘ X = X:= funext fun i=> H _ (by simp [U,V,X])
  have ht := (h.moves (n+2) J U X).symm
  rw [hJ,hx] at ht; exact ht
lemma north_budget (p : Breezes F) (x : External I n) (y : place n): fullPlane (north F x y) := by
  let L₁ := ContinuousLinearMap.fst ℝ ℝ ℂ; let L₂ := (room n).comp (ContinuousLinearMap.snd ℝ ℝ ℂ)
  let Z := External I (n+1)
  let L := L₁.prod (L₂.prod (0:ℝ × ℂ →L[ℝ] Z))
  let b := ((0:ℝ),pad n y,(pad n)∘x)
  have he (u : ℝ × ℂ) : b+L u=(u.1,portal n (y,u.2),pad n∘x) := by rw [place.split]; simp [b,L,L₁,L₂]
  unfold north fullPlane
  simp_rw [← he]
  refine comp_affine_bill L b (aboveAxis p) (fun u hu => ⟨mem_univ _,mem_univ _,mem_univ _⟩) ?_ ?_
  · simp_rw [he,Price.back_apply]; exact Bills.const _
  refine bill_byprice fun u _ => ?_
  change _ ≤ Moment _ (b+L u); rw [he]
  change (1+|u.1|)*(1+‖u.2‖) ≤ (1+|u.1|)*((1+‖portal n (y,u.2)‖)*1); rw [mul_one]; gcongr
  nlinarith [squared (n:=n) (y,u.2),sq_nonneg ‖y‖,norm_nonneg (portal n (y,u.2)),norm_nonneg u.2]

private lemma regularity {x : External I n} (h : Texture F) (p : Breezes F) (D : ℂ) :
    Integrable (fun y:place n => dimensional (lifting n F) (y,x) (D-2*n)) := by
  have hs : EvenOn (Domain n univ) (lifting n F) := fun x _ => symmetric h n x (mem_univ _)
  have hx := (internal (L:=0) (b:=D) (p:=ticket (@id (External I n))) isOpen_univ
    (show ContinuousOn (fun z:External I n=>1+‖z‖) univ from (continuous_const.add continuous_norm).continuousOn)
    (aboveAxis p) hs ‖D‖ (by simp)).1 x (mem_univ _); simp only [zero_apply,add_zero] at hx; exact hx

theorem padding (p : Breezes F) (h : Texture F) (x : External I n) (D : ℂ): omega (n+1) F (pad n ∘ x) D = omega n F x D := by
  let X := pad n ∘ x; let W:= D- 2*((n+1:ℕ):ℂ)
  let V(y:place (n+1)) := dimensional (lifting (n+1) F) (y,X) W
  let T:= portal n; have he:= volumeThrough n; have hx := (regularity (x:=X) h p D)
  have hu : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  unfold omega inside; change _*(∫ y,V y)=_
  rw [← he.integral_comp hu,Measure.volume_eq_prod (place n) ℂ,integral_prod]
  · have hb (y:place n): (∫ z:ℂ,V (portal n (y,z)))=(π:ℂ)*dimensional (lifting n F) (y,x) (D-2*n):= by
      rw [← show W+2=D-2*n by unfold W; push_cast; ring]
      rw [congr_fun (recorded (f:=lifting n F) (g:=north F x y) (y:=0) (linking h x y)) _,← gradation (north_budget p x y) (north_round h x y)]
      exact integral_congr_ae (Eventually.of_forall fun z=>congr_fun (recorded (f:=lifting (n+1) F) (g:=north F x y) (x:=(portal n (y,z),X)) (y:=z) (fun t=>rfl)) _)
    change _*(∫ y:place n, ∫ z:ℂ,V (portal n (y,z)))=_
    simp_rw [hb]; rw [integral_const_mul,pow_succ]; field_simp
  rw [← Measure.volume_eq_prod]; exact (he.integrable_comp_emb hu).mpr (show Integrable V from hx)

theorem operations (p : Breezes F) (h : Texture F) (D : ℂ): Tensor (fun n x=> omega n F x D) :=
  ⟨fun _ J x=> rotates h D x J, fun _ x=> padding p h x D⟩
-- Especially at four dimensions, after pole subtraction.
theorem projection (p : Breezes F) (h : Texture F) (x : External I n) :
    omega n F x (2*n) = ((π:ℂ)^n)⁻¹ * ∫ y:place n,F n (y,x) := by
  unfold omega
  rw [phys (p:=ticket (@id (External I n))) isOpen_univ
    (show ContinuousOn (fun z:External I n=>1+‖z‖) univ from (continuous_const.add continuous_norm).continuousOn)
    (aboveAxis p) (fun z _=> symmetric h n z (mem_univ _)) (mem_univ _)]
  congr 1; apply integral_congr_ae; filter_upwards with y
  change F _ (portal n (y,((0:ℝ):ℂ)),_)=_; rw [Complex.ofReal_zero]; exact h.agrees n y x
end YM.MSbar.Pole.Ambient
