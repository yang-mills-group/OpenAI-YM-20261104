import YM.MSbar.Pole.Dimension.Interlude

/-! Outer momentum dimension extension. Vertices on external lists of genuine vector data.
Strip MS factors. No specialization to ≤4 independent polarizations. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Ambient
open Set Function Filter MeasureTheory place Radial
open scoped Topology InnerProductSpace ContDiff Classical BigOperators Real
variable {I : Type} [Fintype I] {n : ℕ}

/-- Position and polarization can use this same indexing, union when appropriate. -/
abbrev External (I : Type) (n : ℕ) := I → place n
abbrev Cloud (I : Type) := ∀ n : ℕ, External I n → ℂ
abbrev Screened (I : Type) := ∀ n, place n × External I n → ℂ

structure Tensor (F : Cloud I) : Prop where
  moves n (J : place n≃ₗᵢ[ℝ] place n) (x : External I n) : F n (J ∘ x) = F n x
  agrees n x : F (n+1) (pad n ∘ x) = F n x
structure Texture (F : Screened I) : Prop where
  moves n (J : place n ≃ₗᵢ[ℝ] place n) (p : place n) (x : External I n) :
    F n (J p,J ∘ x)=F n (p,x)
  agrees n p x : F (n+1) (pad n p,pad n ∘ x)=F n (p,x)

def lifting (n:ℕ) (F : Screened I) (x : ℝ × (place n × External I n)) :=
    F (n+1) (portal n (x.2.1,x.1),pad n ∘ x.2.2)

def omega (n:ℕ) (F : Screened I) (x : External I n) (D : ℂ) := inside n (lifting n F) x D

variable {F : Screened I}
omit [Fintype I] in
lemma symmetric (h : Texture F) (n : ℕ) : EvenOn univ (lifting n F) := by
  intro x _ t
  let u : place (n+1) := portal n (x.1,t); let v : place (n+1) := portal n (x.1,-t)
  have he : ‖u‖^2 = ‖v‖^2 := by unfold u v; rw [squared,squared]; simp
  obtain ⟨J,hJ,H⟩:= place.sphere he
  have hz i : J (pad n (x.2 i)) = pad n (x.2 i) := H _ (by unfold u v; simp)
  change F (n+1) (portal n (x.1,↑(-t)),pad n∘x.2)= F (n+1) (u,pad n∘x.2)
  push_cast; rw [← h.moves (n+1) J u (pad n ∘ x.2),hJ]; congr 2; funext i; exact (hz i).symm

lemma rotates (h : Texture F) (D : ℂ) (x : External I n) (J : place n ≃ₗᵢ[ℝ] place n): omega n F (J ∘ x) D = omega n F x D := by
  unfold omega inside
  rw [← J.measurePreserving.integral_comp J.toMeasurableEquiv.measurableEmbedding (fun u => dimensional (lifting n F) (u,J ∘ x) _)]
  congr 1; apply integral_congr_ae; filter_upwards with i
  refine congr_fun (recorded (f:=lifting n F) (g:=lifting n F) (x:=(J i,J ∘ x)) (y:=(i,x)) ?_) _
  intro t; change F (n+1) (portal n (J i,t),pad n ∘ (J ∘ x)) = F (n+1) (portal n (i,t),pad n ∘ x)
  rw [← h.moves (n+1) (grow J) (portal n (i,(t:ℂ))) (pad n∘x),grow_apply]; congr 2; funext k; simp

/-- Upright all-external-values tensor identity per fiber; analytic equality later
may use only on pole-free families but dimensional rule well-posed whenever
`Breezes`. -/
def Breezes (F : Screened I) := ∀ n, Packet (Domain n univ) (ticket (@Prod.snd (place n) (External I n))) (ticket (@Prod.fst (place n) (External I n))) (F n)

private def padAll (n : ℕ) : External I n →L[ℝ] External I (n+1) := ContinuousLinearMap.pi fun i : I=> (pad n).comp (ContinuousLinearMap.proj i)

private lemma kinetic (p : place n) (t : ℝ): 1+‖p‖ ≤ 1+‖portal n (p,(t:ℂ))‖ := by
  linarith only [show ‖p‖ ≤ ‖portal n (p,(t:ℂ))‖ by nlinarith [squared (n:=n) (p,(t:ℂ)),sq_nonneg ‖(t:ℂ)‖,norm_nonneg (portal n (p,(t:ℂ))),norm_nonneg p]]
private lemma radial_gain (p : place n) (t : ℝ): 1+‖t‖ ≤ 1+‖portal n (p,(t:ℂ))‖ := by
  have he := squared (n:=n) (p,(t:ℂ)); change _=‖p‖^2+‖(t:ℂ)‖^2 at he; rw [Complex.norm_real] at he
  nlinarith [he,sq_nonneg ‖p‖,norm_nonneg (portal n (p,(t:ℂ))),norm_nonneg t]
lemma aboveAxis (hp : Breezes F) : Packet (univ ×ˢ Domain n univ) (((ticket (@id (External I n))).back (@Prod.snd (place n) (External I n))).back Prod.snd)
    (Moment (screen n 1)) (lifting n F) := by
  let V := place n × External I n; let D : ℝ × V →L[ℝ] V:= ContinuousLinearMap.snd ..
  let P := ContinuousLinearMap.fst ℝ (place n) (External I n); let Y := ContinuousLinearMap.snd ℝ (place n) (External I n)
  let A : ℝ × V→L[ℝ]ℂ:= Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ V)
  let B : ℝ × V→L[ℝ]place (n+1) × External I (n+1):=((portal n).toContinuousLinearMap.comp ((P.comp D).prod A)).prod (padAll n |>.comp (Y.comp D))
  let p := (((ticket (@id (External I n))).back (@Prod.snd (place n) (External I n))).back (@Prod.snd ℝ (place n×External I n))); let q:= Moment (screen n (1:Price (External I n)))
  let K : Set (ℝ × V) := univ ×ˢ Domain n univ
  have ht := comp_affine_bill (F':=F (n+1)) (p:=p) (q:=q) (U:=K) B 0 (hp (n+1)) (by intro x _; exact mem_prod.mpr ⟨mem_univ _,mem_univ _⟩) ?_ ?_
  · simp only [zero_add] at ht; exact ht
  · let C : ℝ := ‖padAll (I:=I) n‖
    have hc : 0≤C:= norm_nonneg _
    refine bill_single (C:=1+C) (l:=1) (by positivity) (fun x hx => ?_); rw [zero_add]
    obtain ⟨t,y,z⟩:= x
    change ‖1+‖padAll n z‖‖≤(1+C)*(1+‖z‖)^1
    rw [pow_one,Real.norm_of_nonneg (by positivity)]; linarith [(padAll n).le_opNorm z,norm_nonneg z] -- defeq?
  refine bill_single (C:=1) (l:=2) (zero_le_one) fun x hx=>?_
  change ‖q x‖ ≤ 1*(ticket (@Prod.fst _ _) (0+B x))^2
  rw [Real.norm_of_nonneg (q.pos _).le,zero_add,one_mul]; obtain ⟨t,y,z⟩:= x
  change (1+‖t‖)*( (1+‖y‖)*1)≤ (1+‖portal n (y,(t:ℂ))‖)^2
  rw [pow_two,mul_one]; exact mul_le_mul (radial_gain _ _) (kinetic _ _) (by positivity) (by positivity)
end YM.MSbar.Pole.Ambient
