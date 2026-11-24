import YM.UVExt.ResetRays

/-! Quadratic discrepancy of loop vs incoming and charged discrepancy of α tested on real wave cylinders. Bound before changing volume. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Set Function Filter Lattice Tree Laurent Wilson Exterior RG Tensor Precision Bid
open scoped BigOperators Topology ContDiff Classical
variable {G : Gauge} {q p : Clip} {c f : Side} {S : StepData c f} {F : Forest S.ratio}
   {t : S.Choices} {U R : ℕ→PathData G} {ρ : ℕ→fieldDir G c 1 → AxisChart G F}
    {Y : ℕ→Matrix (Body 1 f) (Body 1 c) ℝ} {η : ℝ}
variable {U' R' η' ρ' Y'}
variable (L : Slab F U R p q t ρ η Y) (V : Slab F U' R' p q t ρ' η' Y') {H : ChartRatio G} (hH : LocalRatio H)
    (K : ℕ→PathData G) (β : ℕ→ℝ)
    {Θ γ B : ℝ}
structure Thermal (L : Slab F U R p q t ρ η Y) (β : ℕ→ℝ) (bθ : ChartRatio G) (Θ γ B : ℝ) : Prop where
   bound : ∀ᶠ i:ℕ in atTop, FiniteBound F (U i) (R i) p q (β i) bθ (ρ i) Θ γ B

-- scalar ray for Wave
omit L V hH K
private lemma wave_dilution (i) (σ : TypeFace 1→G.ColorIndex→ℂ) (a : ℝ) : wave (G:=G) (c:=c) i ((fun b j=> (a:ℂ)*σ b j))= a • wave i σ := funext fun z=> by
     ext j; change (Bloch.cell i z.1 * ((a:ℂ)*σ z.2 j)).re = a * (Bloch.cell i z.1 * σ z.2 j).re; rw [mul_left_comm]; simp
variable (hσ : TypeFace 1 → G.ColorIndex → ℂ)
private lemma prices (A Q : T (Dir G c) ℝ 2) {e} (h : ∀ i j (σ τ : TypeFace 1→G.ColorIndex→ℂ), (∀ k l, ‖σ k l‖≤1) → (∀ k l,‖τ k l‖ ≤ 1) → |A ![wave i σ,wave j τ]-Q ![wave i σ,wave j τ]| ≤ e) (i : Site c) (τ σ : TypeFace 1→G.ColorIndex→ℂ) (h₁ : ∀ k l, ‖σ k l‖≤1) (h₂ : ∀ k l, ‖τ k l‖≤1) (j : Site c) :
    let u := wave i σ + wave j τ
    |A ![u,u] - Q ![u,u]| ≤ 4*e := by
    intro u
    let u' := wave i σ; let t := wave j τ
    have hh (p : Tensor.T (Dir G c) ℝ 2) (x : Dir G c) : p ![u,x]=p ![u',x]+p ![t,x] := by unfold u; change (p.curryLeft (u'+t)) (![x]:Fin 1→Dir G c)= (p.curryLeft u') (![x]) + p.curryLeft t (![x]); rw [map_add]; rfl
    have hf (p : Tensor.T (Dir G c) ℝ 2) (x : Dir G c) : p ![x,u]=p ![x,u']+p ![x,t]  := by rw [← snoc_one x u,←snoc_one x u',←snoc_one x t]; unfold u; change (p.curryRight (![x]:Fin 1→Dir G c)) (u'+t) = _; rw [map_add]; rfl
    have h₁' := (abs_le.mp <| h i i _ _ h₁ h₁); have h₂' := (abs_le.mp <| h i j _ _ h₁ h₂); have h₃ := (abs_le.mp <| h j i _ _ h₂ h₁); have h₄ := (abs_le.mp <| h j j _ _ h₂ h₂)
    rw [hh A u, hh Q u, hf A u',hf Q u',hf A t,hf Q t]
    unfold u' t; rw [abs_le]; constructor <;> linarith
include L
variable (hW : TypeFace 1→G.ColorIndex→ℂ) {Θ γ B : ℝ}
def tolerance (c : Side) (Θ γ B : ℝ) : ℝ := (Fintype.card (Site c):ℝ)*Θ*B*Real.exp (-γ*c.val)
private lemma wave_taxes (h : Thermal L β H Θ γ B) (j d : Site c) (σ : TypeFace 1 → G.ColorIndex → ℂ) (τ : TypeFace 1→G.ColorIndex→ℂ) (h₁ : ∀ k l, ‖σ k l‖≤1) (h₂ : ∀ k l,‖τ k l‖≤1) : let w := (wave j σ + wave d τ); ∀ᶠ i in atTop,
     |tag 2 (L.thermalRay H w i) - Slab.finalCover R q β w i| ≤ 4*(tolerance c Θ γ B) := by
    intro w; apply h.bound.mono; intro i hi
    let f := thermal F t p (U i) (ρ i) H
    let Q := (draft (c:=c) (β i) (R i) q)
    let A := iteratedFDeriv ℝ 2 f 0; let C := iteratedFDeriv ℝ 2 Q 0
    change |tag 2 (fun z:ℝ=> f (z • w)) - C ![w,w]| ≤ _
    have hG := fun i j σ' τ' h₁ h₂=>prices A C (hi.wave_price t) i τ' σ' h₁ h₂ j
    rw [show tag 2 (fun z:ℝ=> f (z•w))=Tensor.diagonal A w from ray_tag _ ((hi.born t).of_le (by simp: ↑(2:ℕ)≤(ω:ℕ∞ω))) w, show Tensor.diagonal A w=A ![w,w] from congr_arg A (constant_two w)]; exact (hG _ _ _ _ h₁ h₂)

variable {hσ hC hΛ hμ hZ hA uσ uC uΛ uμ uZ uA : ℝ} {K V' K' T : Shadow G} (hU : Passing U K hσ hC hΛ p) (hP : Passing R K' hμ hZ hA q) (hB : Passing U' V' uσ uC uΛ p) (hD : Passing R' T uμ uZ uA q)
include L V hH hU hP hD hB
variable {β' : ℕ→ℝ} {x y : ℝ}
lemma true_wave_bill (h : Thermal L β H Θ γ B) (hh : Thermal V β' H Θ γ B) (ht : Junction L.inFine V.inFine 4) {Z} (hY : Tendsto Y atTop (𝓝 Z))
     (he : 0<η) (hv : 0<η') (j d : Site c) (σ τ : TypeFace 1→G.ColorIndex→ℂ) (h₁ : ∀ k l, ‖σ k l‖≤1) (h₂ : ∀ k l, ‖τ k l‖≤1)
     (hz : Tendsto β atTop (𝓝 x)) (hz' : Tendsto β' atTop (𝓝 y)) :
    let w := (wave j σ + wave d τ)
    |x*Tensor.diagonal (hP.economicTensor c 2) w - y*Tensor.diagonal (hD.economicTensor c 2) w + discrep (hP.spiralTensor c 2) (hD.spiralTensor c 2) w - discrep (hU.spiralTensor f 2) (hB.spiralTensor f 2) (polish Z w)| ≤ 8*tolerance c Θ γ B := by
    intro w
    apply le_trans (le_of_tendsto ((Slab.reset_limit L V hU hP hB hD β β' w hz hz' |>.sub (Slab.thermal_ray_limit L V hU hB hH ht he hv w hY)).abs) _) le_rfl
    filter_upwards [wave_taxes L β h j d σ τ h₁ h₂, wave_taxes V β' hh j d σ τ h₁ h₂] with n h₁ h₂
    let e := tolerance c Θ γ B
    let u := tag 2 (L.thermalRay H w n); let v := tag 2 (V.thermalRay H w n); let p := Slab.finalCover R q β w n; let Q := Slab.finalCover R' q β' w n
    change |p-Q-(u-v)| ≤ 8*e; change |u-p| ≤ 4*e at h₁; change |v-Q| ≤ 4*e at h₂
    exact (abs_le.mpr ⟨by linarith [abs_le.mp h₁ |>.1,abs_le.mp h₁ |>.2, abs_le.mp h₂|>.1,abs_le.mp h₂|>.2],by linarith [abs_le.mp h₁ |>.1,abs_le.mp h₁ |>.2,abs_le.mp h₂|>.1,abs_le.mp h₂|>.2]⟩)
end YM.UVExt.Paths
