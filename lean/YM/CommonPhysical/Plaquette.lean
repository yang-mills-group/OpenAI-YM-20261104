import YM.CommonPhysical.CurvatureStart
import YM.Extra.WILSON_STARTUP.Face

/-! Actual plaquette truncation for the startup RG representation.
Proof follows and extends Face. The exponent denominator in perturbative
counting shifts these orders by two (`β = g⁻²`). -/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup
open Function Filter Work Tensor Next.Fluctuations Lattice Wilson RG
open scoped ContDiff Topology Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n : Side} (J : ℕ)

def leftOver (p : Cell n) (U : Config G n) := unspent J (faceValue U p)

theorem leftOver_jet (p : Cell n) (U : Config G n) (l : List (Directions G n)) :
    leftDerivs (leftOver J p) l U = Quad.strokes J (l.map (· ∘ edges p)) (Quad.mat (U ∘ edges p)) := by
  induction l generalizing U with
  | nil => rw [leftDerivs, List.map_nil, Quad.strokes, comp_apply, Quad.read_actual, Quad.tail_actual, read_edges]; rfl
  | cons a l ih =>
    simp only [leftDerivs, List.map_cons, ih, Quad.strokes]
    exact congr_arg (deriv · 0) (funext fun t => congr_arg _ (funext fun i : Fin 4 => G.mat_mul ..))

theorem leftOver_price (G : Gauge) (k P : ℕ) : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧
    ∀ (b : BudgetPoint), b.power = P → b.order = k → b.threshold ≤ δ → ∀ (n : Side) (p : Cell n) (o : Site n),
      o ∈ touched p → b.supBounds o (touched p) (leftOver (G:=G) J p) (C*b.threshold^(J+1)) := by
  let Jlocal := Fin (k+1)
  choose c d hc hd h' h using fun i : Jlocal => Quad.small_tail J G i.val ((1+4)^P)
  obtain ⟨i,hi,he⟩ := Finset.exists_min_image Finset.univ d Finset.univ_nonempty
  let C := 1 + ∑ j : Jlocal, c j
  have hC : 0 < C := add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => (hc i).le)
  refine ⟨C,d i,hC, hd i, h' i, fun b hb hk ht n p o ho => ⟨mul_nonneg hC.le (pow_nonneg b.threshold_pos.le _),?_⟩⟩
  intro U hu l hl hA
  rw [hk] at hl
  let j : Jlocal := ⟨l.length, Nat.lt_succ_of_le hl⟩
  let a (i : Fin j.val) := l.get i ∘ edges p
  have ha : ‖a‖ ≤ b.threshold*(1+4:ℝ)^P := by
    have hh := b.threshold_pos
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro s
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro f
    apply ((hA _ (l.get_mem s)) (edges p f)).trans
    rw [hb]; gcongr
    exact_mod_cast (separation_triangle (edges p f).1 p.1 o).trans (Nat.add_le_add (visit_near p (edges_visit p f))
      ((separation_comm _ _) ▸ visit_near p ho))
  have H := h j (U ∘ edges p) a _ b.threshold_pos (ht.trans (he j (Finset.mem_univ j))) ha ((read_edges p U).symm ▸ healthy_chord p U hu)
  have hcj : c j ≤ C := (Finset.single_le_sum (fun i _ => (hc i).le) (Finset.mem_univ j)).trans
    (le_add_of_nonneg_left zero_le_one)
  rw [leftOver_jet, ← show List.ofFn a = l.map (· ∘ edges p) from (List.map_ofFn (g:=(· ∘ edges p)) (f:=l.get)).symm.trans (by rw [List.ofFn_get])]
  exact H.trans (mul_le_mul_of_nonneg_right hcj (pow_nonneg b.threshold_pos.le _))


theorem unspent_conj (u v : G.El) : unspent J (u*v*u⁻¹) = unspent J v := by
   unfold unspent; rw [G.price_conj,G.curvature_conjugate]
   unfold G05.blockTaylor; simp only [Finset.sum_apply]
   apply congr_arg; exact Finset.sum_congr rfl fun i _ => coeff_adjoint u i (fun _ => G.curvature v)

lemma coeff_neg (v : G.Color) (j : ℕ) : diagonal (coeff (inK G) j 0) (-v) = diagonal (coeff (inK G) j 0) v := by
   rcases Nat.even_or_odd j with h|h
   · rw [← neg_one_smul ℝ v, homogeneous, h.neg_one_pow]; exact one_smul ..
   rw [odd_diagonal _ j h,odd_diagonal _ j h]

theorem unspent_inv (v : G.El) : unspent J v⁻¹ = unspent J v := by
   unfold unspent; rw [G.price_inv,G.curvature_inv]
   unfold G05.blockTaylor; simp only [Finset.sum_apply,coeff_neg]

theorem leftOver_smooth (p : Cell n) (U : Config G n) : ContDiff ℝ ω (leftOver (G:=G) J p ∘ increment U) := by
  simp_rw [comp_def, leftOver, ← Quad.tail_actual]
  exact (Quad.tailMat_diff J).comp (mat_face_inc ..)

theorem leftOver_regular (p : Cell n) (b : BudgetPoint) : b.Regular (touched p) (leftOver (G:=G) J p) := by
  have h (U : Config G n) := ((leftOver_smooth J p U).of_le (m:=(b.order:ℕ∞)) le_top).contDiffAt (x:=0)
  refine ⟨fun U V h => congr_arg (unspent J) (face_local p U V h), Continuous.measurable ?_, ?_,fun U _ => h U,
    fun U _ a l hl => Next.Foundations.left_has a hl (h U)⟩
  · change Continuous fun U => leftOver J p U
    simp only [leftOver,← Quad.tail_actual]; exact (Quad.tailMat_diff J).continuous.comp
      (G.continuous_mat.comp (continuous_travel ..))
  intro k U; exact (congr_arg (unspent J) (face_gauge k U p)).trans (unspent_conj ..)

theorem leftOver_flat (p : Cell n) : FlatAt (J+1) (leftOver (G:=G) J p ∘ increment 1) 0 := by
  refine unspentJet J (fun v => faceValue (increment 1 v) p) ?_ (mat_face_inc .. |>.contDiffAt)
  rw [Work.G07.at_zero_increment,face_one]

theorem leftOver_one (p : Cell n) : leftOver (G:=G) J p 1 = 0 := by
  have h := congr_arg (Tensor.diagonal · (0:Directions G n)) (leftOver_flat J p 0 (by omega))
  simpa [Tensor.diagonal,comp_def,G07.at_zero_increment] using! h

theorem leftOver_hess (hJ : 2 ≤ J) (p : Cell n) (x y : Directions G n) : logHessian (leftOver (G:=G) J p) x y = 0 :=
  congr_arg (fun u : Tensor.T (Directions G n) ℝ 2 => u ![x,y]) (leftOver_flat J p 2 (by omega))

theorem leftOver_send (p : Cell n) (s : Signed) (x : Site n) (U : Config G n) :
    leftOver J (Face.send s x p) U = leftOver J p (pull s x U) :=
  (Face.send_price U p s x (unspent J) (unspent_inv J) (fun v u => unspent_conj J u v)).symm
end YM.WilsonStartup
