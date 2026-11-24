import YM.SchemeConversionRG11.Maxwell.Loom

/-! # Force each assigned isometry onto the normalizer track. Test real Cartan
three form at weight six. Only at the positions of the free polynomial, no extension. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Corona
open Function Filter MeasureTheory Metric Maxwell Maxwell.Free Wick Tensor Set MvPolynomial
open scoped Topology BigOperators RealInnerProductSpace InnerProduct ComplexOrder

variable {G : Gauge}

def arch (x y z : G.Color) := ⟪x,G.ad y z⟫
def harrow (G : Gauge) (p q r : Flavor 0) := ∑ i : G.ColorIndex, ∑ j : G.ColorIndex, ∑ k : G.ColorIndex,
    (arch (unitColor G i) (unitColor G j) (unitColor G k):ℂ) • (bit p i * bit q j * bit r k)

def vase (G : Gauge) := harrow G (cell 0 1) (cell 0 2) (cell 0 3)
lemma harrow_at (p q r : Flavor 0) (A : TaylorTower G) : Maxwell.probe A (harrow G p q r)=
    (↑(arch (available (A 0) p) (available (A 0) q) (available (A 0) r)):ℂ) := by
  let x := available (A 0) p; let y := available (A 0) q; let z := available (A 0) r
  change _ =(↑(arch x y z):ℂ)
  conv_rhs => rw [← color_sum x,←color_sum y, ←color_sum z]
  unfold arch; simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, sum_inner,
    real_inner_smul_left,Complex.ofReal_sum,Complex.ofReal_mul]
  unfold harrow
  simp only [map_sum,map_smul,map_mul,smul_eq_mul,inner_sum, real_inner_smul_right, Finset.mul_sum,Complex.ofReal_sum,Complex.ofReal_mul]
  conv_rhs => arg 2; ext; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [bit,symbol_test]
  change (↑(arch _ _ _):ℂ)*((x i:ℂ)*(y j:ℂ)*(z k:ℂ))=_
  unfold arch; ring
lemma harrow_real (G : Gauge) (p q r : Flavor 0) : realForm (harrow G p q r)=harrow G p q r := by
  refine equalPol _ _ fun A ↦ ?_; rw [real_eval,harrow_at]; simp
lemma vase_real (G : Gauge) : realForm (vase G)=vase G := harrow_real ..

set_option maxHeartbeats 600000 in
lemma vase_fits {n : ℕ} (h : 6 ≤ n) : vase G∈shellSector G n := by
  let p := cell 0 1; let q:=cell 0 2; let r:=cell 0 3
  refine sector.mpr ⟨?_,fun u ↦ ?_⟩
  · have ht : MvPolynomial.IsWeightedHomogeneous scaleW (harrow G p q r) 6 := by
      unfold harrow; refine IsWeightedHomogeneous.sum _ _ _ (fun i _ ↦ IsWeightedHomogeneous.sum _ _ _ (fun j _ ↦ IsWeightedHomogeneous.sum _ _ _ (fun k _ ↦ ?_)))
      rw [← C_mul']; have hs (p : Flavor 0) (i : G.ColorIndex) : IsWeightedHomogeneous scaleW (bit p i) 2 := symbol_hom (flavor (G:=G) 0 i p) (fun j↦j+2)
      apply IsWeightedHomogeneous.C_mul
      change IsWeightedHomogeneous scaleW (bit p i * bit q j * bit r k) (2+2+2); exact ((hs p i).mul (hs q j)).mul (hs r k)
    rw [lowerCap,mem_restrictSupport_iff]; intro i hi; exact (ht (MvPolynomial.mem_support_iff.mp hi)).le.trans h
  apply equalPol; intro A
  rw [pigment_action]
  change Maxwell.probe (commerce (firm u) A) (harrow G p q r)=Maxwell.probe A (harrow G p q r)
  rw [harrow_at,harrow_at]; unfold commerce; simp only [givens]
  unfold arch; rw [← firmBracket u,(firmFair u).inner]

lemma arbitrary (x y z : G.Color) : ∃ p : TaylorTower G, available (p 0) (cell 0 1)=x ∧ available (p 0) (cell 0 2)=y ∧ available (p 0) (cell 0 3)=z := by
  classical
  let A (a b : Axis) (x : G.Color) := fill 0 x (blade a b 1)
  let X := Pi.single 0 (A 0 1 x+A 0 2 y +A 0 3 z)
  refine ⟨X,?_,?_,?_⟩ <;> unfold X A <;> rw [Pi.single_eq_same] <;> ext1 i
  · change cell 0 1 (faceMap _ (cp i) (_+_+_)) = _; simp only [map_add,which,map_smul,cell_price]; simp (config := { decide := true }) [wedge]
  · change cell 0 2 (faceMap _ (cp i) (_+_+_)) = _; simp only [map_add,which,map_smul,cell_price]; simp (config := { decide := true }) [wedge]
  change cell 0 3 (faceMap _ (cp i) (_+_+_)) = _; simp only [map_add,which,map_smul,cell_price]; simp (config := { decide := true }) [wedge]

lemma vase_forces {R : Door G} (h : Fair R) (H : ∀ A, Maxwell.probe (commerce R A) (vase G)=Maxwell.probe A (vase G)) : bracketForm R := by
  intro x y
  apply ext_inner_left ℝ; intro v; obtain ⟨w,rfl⟩ := h.onto v
  obtain ⟨A,h₁,h₂,h₃⟩ := arbitrary w x y
  have hx := H A; rw [vase,harrow_at,harrow_at] at hx; unfold commerce at hx; simp only [givens,h₁,h₂,h₃] at hx
  rw [h.inner]; exact (Complex.ofReal_injective hx).symm

lemma auto_deriv {f : ℝ→ Door G} {D : Door G} (h : f 0=1) (hd : HasDerivAt f D 0) (ht : ∀ i,bracketForm (f i)) : derivingD G D := by
  intro x y
  let F (x : G.Color) (i:ℝ) := f i x
  have hf (x : G.Color) : HasDerivAt (F x) (D x) 0 := (ContinuousLinearMap.apply ℝ G.Color x).hasFDerivAt.comp_hasDerivAt 0 hd
  let A:= (adh G).toContinuousLinearMap
  have he := (A.hasFDerivAt.comp_hasDerivAt (0:ℝ) (hf x)).clm_apply (hf y)
  have hF x : F x 0=x := by unfold F; rw [h]; rfl
  simp only [Function.comp_apply,hF] at he
  rw [show (fun i ↦ A (F x i) (F y i))=F (G.ad x y) from funext fun i ↦ (ht i x y).symm] at he
  exact (hf _).unique he
lemma ridge_tracks (R : Door G) (h : G.Simple) (hr : Fair R) {n : ℕ} (w : WickPol G) (hw : w∈ shellSector G n)
    (H : ∀ A, Maxwell.probe (commerce R A) w=Maxwell.probe A (vase G)) : R∈ Tracks G := by
  have he u : bracketForm (((R†)*firm (G:=G) u)*R) := by
    refine vase_forces ((hr.back.mul (firmFair _)).mul hr) (fun A ↦ ?_)
    rw [← H,← H A,← commerce_comp]
    rw [show R ∘L _=firm (G:=G) u ∘L R from ?_,commerce_comp]; exact invariant_firm w hw u _
    change R*((R†)*firm u*R)=firm u*R; rw [← mul_assoc, ← mul_assoc,hr.inv', one_mul]
  refine ⟨hr,fun x ↦ innerD h ?_⟩
  let f (t : ℝ) := firm (G.lieExp (t • x))
  have ht : f 0=1 := by simp [f,firm_one]
  have ht' := ((show HasDerivAt f _ (0:ℝ) from firm_flow x).const_mul (R†)).mul_const R
  exact auto_deriv (f:=fun t ↦ (R†)*f t*R) (by rw [ht,mul_one,hr.inv]) ht' fun s ↦ he _
end YM.SchemeConversionRG11.Corona
