import YM.Pert.Triangle.Operators
/-! Invariant labels and identifications with the exact raw sections, since rebase on the undifferentiated curvature space is the identity. Not asserting these are the final mass-independent frames. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 490000
noncomputable section
namespace YM.Pert.Triangle
open Maxwell Labels UVNext UVNext.FreeStress RawLabels Function Lattice Matrix MvPolynomial
open scoped Topology Classical Matrix.Norms.Frobenius
variable {G : Gauge}
-- inner and bracket invariance
lemma inner_adjoint (x y : G.Color) (u : G.El) : inner ℝ (G.adjoint u x) (G.adjoint u y) = inner ℝ x y := FreeStress.adjoint_is_inner ..
lemma conjugate_product (A B : G.Mat) (u : G.El) : G.conjugate u (A * B) = G.conjugate u A * G.conjugate u B := by
  simp only [Gauge.conjugate,mul_assoc]; rw [←mul_assoc (star (G.mat u))]; rw [G.mat_star_mul,one_mul]
lemma bracket_adjoint (x y : G.Color) (u : G.El) : G.ad (G.adjoint u x) (G.adjoint u y) = G.adjoint u (G.ad x y) := by
  apply G.colorMat_injective
  simp only [G.colorMat_ad,G.mat_adjoint]
  rw [←conjugate_product,←conjugate_product]; unfold Gauge.conjugate; simp [sub_mul,mul_sub]
@[simp] lemma read_fan_color (p : Jet G) (u : G.El) (h i) : fanReading h i ((colored u p) 0) = G.adjoint u (fanReading h i (p 0)) := reading_adjoint ..
lemma uMinus_inv (p : Jet G) (u : G.El) : Labels.read (colored u p) (uMinus G) = Labels.read p (uMinus G) := by simp only [read_u, read_fan_color,inner_adjoint]
lemma read_b (A : Jet G) : Labels.read A (bFan G) = ∑ i, ∑ j, ∑ k,(↑(eps3 i j k) : ℂ) * (↑(inner ℝ ((G.ad (fanReading true i (A 0))) (fanReading true j (A 0))) (fanReading true k (A 0))):ℂ) := by
  unfold bFan; simp only [map_sum]; apply Finset.sum_congr rfl; intro i _;apply Finset.sum_congr rfl;intro j _;apply Finset.sum_congr rfl;intro k _; simpa only [map_sum] using (triple_value A i j k _ _ _ rfl rfl rfl)
lemma bFan_inv (p : Jet G) (u : G.El) : Labels.read (colored u p) (bFan G) = Labels.read p (bFan G) := by simp_rw [read_b,read_fan_color,bracket_adjoint,inner_adjoint]

def evenSlot (G :Gauge) : Label G 4 := ⟨uMinus G,uMinus_cap,uMinus_inv⟩
def oddSlot (G :Gauge) : Label G 6 := ⟨bFan G,bFan_cap,bFan_inv⟩
variable (F : Frames G)
section projector
variable {n : ℕ} {p : Label G n}
lemma zero_only (h : ∀ A B : Jet G, A 0=B 0 → Labels.read A p.val = Labels.read B p.val) : physicalLabel F n (enroll F n p)=p := by
  rw [embed_round]; refine Subtype.ext (eval_ext _ _ (fun A=>?_))
  change Labels.read A (changed (rebase G) _)=_; rw [eval_changed]
  exact h _ A (onsite_raw (A 0))
lemma own (h : ∀ A B : Jet G, A 0=B 0 → Labels.read A p.val = Labels.read B p.val) {m : ℕ} (he : n≤m) : Full.sections m F (enroll F m (raiseLabel G he p))=p.val := congrArg Subtype.val (zero_only F (p:=raiseLabel G he p) h)
end projector
lemma even_read {n} (h) : Full.sections n F (enroll F n (raiseLabel G h (evenSlot G)))= (evenSlot G).val := own F (fun A B hb=> by change Labels.read A (uMinus G)=_; simp only [read_u,hb]; exact (read_u B).symm) h
lemma odd_read {n} (h) : Full.sections n F (enroll F n (raiseLabel G h (oddSlot G))) = (oddSlot G).val := own F (fun A B hb=> by change Labels.read A (bFan G) =_; simp only [read_b,hb]; exact (read_b B).symm) h
lemma uMinus_sign : Parity.wash G 4 (evenSlot G)=evenSlot G := by apply Subtype.ext; change Parity.shadow G (uMinus G) = _; unfold uMinus evenSlot; simp [fan_negate,Parity.shadow_C,uMinus]
lemma bFan_sign : Parity.wash G 6 (oddSlot G)= -oddSlot G := by
  apply Subtype.ext
  change Parity.shadow G (bFan G) = - (bFan G)
  unfold bFan triple; simp only [map_sum, ←Finset.sum_neg_distrib, map_mul, Parity.shadow_C,fan_negate,neg_mul_neg,mul_neg,neg_mul,neg_neg]
lemma color_nonzero (hg : G.Simple) : ∃ a b c : G.ColorIndex, colorF a b c ≠ 0 := by
  by_contra! h
  obtain ⟨x,y,he⟩ := hg.nonabelian
  have hz := bracket_expand x y (G.ad x y)
  rw [real_inner_self_eq_norm_sq] at hz; simp [h] at hz -- use simp to get false
  exact he (norm_eq_zero.mp (sq_eq_zero_iff.mp hz.symm))
lemma structure_price (hg : G.Simple) : 0 < ∑ a:G.ColorIndex,∑ b,∑ c,colorF a b c ^ 2 := by
  obtain ⟨a,b,c,he⟩ := color_nonzero hg
  have hp x y z : 0 ≤ colorF (G:=G) x y z ^ 2 := by positivity
  calc
    _ < colorF a b c ^ 2 := sq_pos_of_ne_zero he
    _ ≤ ∑ c,(colorF a b c)^2 := Finset.single_le_sum (f:=fun c=>colorF a b c^2) (fun i (_:i∈ _) => hp a b i) (Finset.mem_univ c)
    _ ≤ ∑ b,∑ c,(colorF a b c)^2 := Finset.single_le_sum (fun i (_:i∈_)=>Finset.sum_nonneg (fun j _=>hp a i j)) (Finset.mem_univ _)
    _ ≤ _ := Finset.single_le_sum (fun i (_:i∈_)=>Finset.sum_nonneg (fun j _=>Finset.sum_nonneg (fun k _=>hp i j k))) (Finset.mem_univ _)
end YM.Pert.Triangle
