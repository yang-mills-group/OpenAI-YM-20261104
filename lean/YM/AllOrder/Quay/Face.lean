import YM.AllOrder.Quay.Roy
/-! Adapt face estimate from Extra.WILSON_STARTUP.Face -/
noncomputable section
set_option autoImplicit false
namespace YM.AllOrder.Quay
open Function Filter Work Tensor Next.Fluctuations Lattice Wilson RG
open WilsonStartup WilsonStartup.Quad Floe Floe.Crest
open scoped ContDiff Topology Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n : Side}
variable (m:ℕ)
variable (G)

def errorW (p : Cell n) (U : Config G n) := short m (faceValue U p)

variable {G}

theorem errorW_jet (p : Cell n) (U : Config G n) (l : List (Directions G n)) :
    leftDerivs (errorW G m p) l U = Roy.jet m (l.map (· ∘ edges p)) (Quad.mat (U ∘ edges p)) := by
  induction l generalizing U with
  | nil => rw [leftDerivs, List.map_nil, Roy.jet, comp_apply, Quad.read_actual, PhaseK.ambient_actual, read_edges]; rfl
  | cons a l ih =>
    simp only [leftDerivs, List.map_cons, ih, Roy.jet]
    exact congr_arg (deriv · 0) (funext fun t => congr_arg _ (funext fun i : Fin 4 => G.mat_mul ..))

theorem errorW_price (G : Gauge) (k P : ℕ) : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧
    ∀ (b : BudgetPoint), b.power = P → b.order = k → b.threshold ≤ δ → ∀ (n : Side) (p : Cell n) (o : Site n),
      o ∈ touched p → b.supBounds o (touched p) (errorW G m p) (C*b.threshold^(m+5)) := by
  let J := Fin (k+1)
  choose c d hc hd h' h using fun i : J => Roy.small_jet m G i.val ((1+4)^P)
  obtain ⟨i,hi,he⟩ := Finset.exists_min_image Finset.univ d Finset.univ_nonempty
  let C := 1 + ∑ j : J, c j
  have hC : 0 < C := add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => (hc i).le)
  refine ⟨C,d i,hC, hd i, h' i, fun b hb hk ht n p o ho => ⟨mul_nonneg hC.le (pow_nonneg b.threshold_pos.le _),?_⟩⟩
  intro U hu l hl hA
  rw [hk] at hl
  let j : J := ⟨l.length, Nat.lt_succ_of_le hl⟩
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
  rw [errorW_jet m, ← show List.ofFn a = l.map (· ∘ edges p) from (List.map_ofFn (g:=(· ∘ edges p)) (f:=l.get)).symm.trans (by rw [List.ofFn_get])]
  exact H.trans (mul_le_mul_of_nonneg_right hcj (pow_nonneg b.threshold_pos.le _))

theorem errorW_smooth (p : Cell n) (U : Config G n) : ContDiff ℝ ω (errorW G m p ∘ increment U) := by
  simp_rw [comp_def, errorW, ← PhaseK.ambient_actual]
  exact (PhaseK.diff m).comp (mat_face_inc ..)


theorem short_conjugate (m:ℕ)(u v : G.El) : short m (u*v*u⁻¹) = short m v := by unfold short Crest.fill; rw [surplus_conjugate]; simp_rw [channel_conj]
theorem short_inv (m:ℕ)(u:G.El): short m u⁻¹= short m u:= by unfold short Crest.fill; rw [surplus_inv]; simp_rw [channel_neg]
theorem errorW_regular (p : Cell n) (b : BudgetPoint) : b.Regular (touched p) (errorW G m p) := by
  have h (U : Config G n) := ((errorW_smooth m p U).of_le (m:=(b.order:ℕ∞)) le_top).contDiffAt (x:=0)
  refine ⟨fun U V h => congr_arg (short m) (face_local p U V h), Continuous.measurable ?_, ?_,fun U _ => h U,
    fun U _ a l hl => Next.Foundations.left_has a hl (h U)⟩
  · change Continuous fun U => errorW G m p U
    simp only [errorW,← PhaseK.ambient_actual]; exact (PhaseK.diff m).continuous.comp
      (G.continuous_mat.comp (continuous_travel ..))
  intro k U; exact (congr_arg (short m) (face_gauge k U p)).trans (short_conjugate ..)

theorem errorW_flat (p : Cell n) : FlatAt (m+5) (errorW G m p ∘ increment 1) 0 := by
  refine collation (fun v => faceValue (increment 1 v) p) ?_ (mat_face_inc .. |>.contDiffAt) m
  rw [Work.G07.at_zero_increment,face_one]

theorem errorW_one (p : Cell n) : errorW G m p 1 = 0 := by
  have h := congr_arg (Tensor.diagonal · (0:Directions G n)) (errorW_flat m p 0 (by omega))
  simpa [Tensor.diagonal,comp_def,G07.at_zero_increment] using! h

theorem errorW_hess (p : Cell n) (x y : Directions G n) : logHessian (errorW G m p) x y = 0 :=
  congr_arg (fun u : Tensor.T (Directions G n) ℝ 2 => u ![x,y]) (errorW_flat m p 2 (by omega))

theorem errorW_send (p : Cell n) (s : Signed) (x : Site n) (U : Config G n) :
    errorW G m (Face.send s x p) U = errorW G m p (pull s x U) :=
  (Face.send_price U p s x (short m) (short_inv m) (fun v u => short_conjugate m u v)).symm

end YM.AllOrder.Quay
