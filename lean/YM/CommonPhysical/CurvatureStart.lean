import YM.Extra.WILSON_STARTUP.Ink

/-!
# Independent expansion at Wilson top

Arbitrary curvature order J (Taylor *coefficients*, use Tensor convention).
Comparison is charged on the actual masked representation. The small
variable here is *plaquette* chord, not link, and cut at Health threshold,
including equality. Proof adapts WilsonStartup's fourth-order helpers from
Residual, generalizing all-order without changing the derivative budget.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup
open Function Filter Work Tensor Next.Fluctuations Lattice Wilson RG
open scoped ContDiff Topology Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge}

/-- Remainder of the Wilson face action in *curvature* chart. -/
def unspent (J : ℕ) (u : G.El) := G.price u - G05.blockTaylor J (inK G) (G.curvature u)

/-- Relative to the fixed fourth-order construction, the analytic model. -/
def opening (J : ℕ) (u : G.El) := G05.blockTaylor J (inK G) (G.curvature u) - G05.blockTaylor 4 (inK G) (G.curvature u)

theorem surplus_split (u : G.El) (J:ℕ) : surplus u = opening J u + unspent J u := by
   unfold surplus opening unspent
   rw [convert_taylor]; ring

/-- Increasing the order adds the corresponding homogeneous *coefficient*. -/
theorem opening_succ (J:ℕ) (u : G.El) : opening (J+1) u = opening J u + diagonal (coeff (inK G) (J+1) 0) (G.curvature u) := by
   unfold opening
   have he (x : G.Color) : G05.blockTaylor (J+1) (inK G) x = G05.blockTaylor J (inK G) x + diagonal (coeff (inK G) (J+1) 0) x := by
     unfold G05.blockTaylor; rw[Finset.sum_range_succ,Pi.add_apply]
   rw [he]; ring

theorem unspentJet (J : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : E → G.El)
    (h : u 0 = 1) (hm : ContDiffAt ℝ ω (fun v => G.mat (u v)) 0) : FlatAt (J+1) (unspent J ∘ u) 0 := by
  have hc : ContinuousAt u 0 := (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.continuousAt_iff.mpr hm.continuousAt
  let k := fun x => G.curvature (u x)
  have hz : k 0 = 0 := by simp only [k,h,G.curvature_unit]
  refine FlatAt.congr (g := unspent J ∘ u)
    (FlatAt.comp (f:=inK G - G05.blockTaylor J (inK G)) (u:=k)
       (hz.symm ▸ flat_sub_taylor _ J (inK_diff.of_le le_top))
       (by rw [hz]; exact (inK_diff.of_le le_top).sub (G05.blockTaylor_contDiff .. |>.contDiffAt))
       ((curvature_diff_mat u 0 hm).of_le le_top)) ?_
  filter_upwards [(show Tendsto u (𝓝 0) (𝓝 1) from h ▸ hc.tendsto).eventually (recover_left G)] with x hx
  simp only [comp_apply, Pi.sub_apply, inK,k,hx,unspent]

namespace Quad
variable (J : ℕ)

def tailMat (X : G.Mat) := distMat X - G05.blockTaylor J (inK G) (kMat X)

theorem tail_actual (u : G.El) : tailMat J (G.mat u) = unspent J u := by
  have he := surplus_actual u
  simp only [surplusMat,surplus,k_actual] at he
  rw [tailMat,unspent,k_actual]; linarith

@[fun_prop] theorem tailMat_diff : ContDiff ℝ ω (tailMat (G:=G) J) := by
  have he : ContDiff ℝ ω (distMat (G:=G)) := (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const _).div_const _
  exact he.sub ((G05.blockTaylor_contDiff ..).comp kMat_diff)

def strokes : List (Dir G) → Space G → ℝ
  | [] => tailMat J ∘ readMat
  | a :: l => fun X => deriv (fun t : ℝ => strokes l (spin (t • a) X)) 0
theorem strokes_diff (k : ℕ) : ContDiff ℝ ω fun p : (Fin k → Dir G) × Space G => strokes J (List.ofFn p.1) p.2 := by
  induction k with
  | zero =>
    simp only [List.ofFn_zero, strokes]
    exact ((tailMat_diff J).comp readMat_diff).comp contDiff_snd
  | succ k ih =>
    let V (p : (Fin (k+1) → Dir G) × Space G) (s : ℝ) := strokes J (List.ofFn (Fin.tail p.1)) (spin (s • p.1 0) p.2)
    have ht : ContDiff ℝ ω (uncurry V) := by
      exact ih.comp ((contDiff_pi.mpr fun i => (contDiff_apply ..).comp contDiff_fst.fst).prodMk
        (spin_diff.comp ((contDiff_snd.smul ((contDiff_apply ..).comp contDiff_fst.fst)).prodMk contDiff_fst.snd)))
    simp only [List.ofFn_succ,strokes, deriv]
    exact (ht.fderiv (g:=fun _ => 0) contDiff_const le_top).clm_apply (g:=fun _ => (1:ℝ)) contDiff_const

theorem strokes_smul (r : ℝ) (l : List (Dir G)) (X : Space G) :
    strokes J (l.map (fun a => r • a)) X = r^l.length * strokes J l X := by
  induction l generalizing X with
  | nil => simp [strokes]
  | cons a l ih =>
    simp only [List.map_cons, strokes, List.length_cons, ih, smul_smul, mul_comm _ r,
      deriv_const_mul_field, deriv_comp_mul_left r (fun t => strokes J l (spin (t • a) X)),mul_zero,smul_eq_mul,pow_succ,mul_assoc]
    ring

/-- Each differentiation can reduce the vanishing order by at most one along any
smooth family of actual links with base curvature element identity (not merely k=0). -/
theorem strokes_flat (l : List (Dir G)) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E → Group G) (h : ContDiff ℝ ω (mat ∘ U)) (hz : read (U 0) = 1) :
    FlatAt (J+1-l.length) (strokes J l ∘ mat ∘ U) 0 := by
  induction l generalizing E with
  | nil =>
    rw [show strokes J ([]:List (Dir G)) ∘ mat ∘ U = unspent J ∘ read ∘ U from funext fun x => by simp only [strokes,comp_apply,read_actual,tail_actual]]
    exact unspentJet J _ hz (by
      simp only [comp_apply, ← read_actual]
      exact (readMat_diff.comp h).contDiffAt)
  | cons a l ih =>
    let Q (v : E × ℝ) (i : Fin 4) := G.lieExp (v.2 • a i) * U v.1 i
    have hm : mat ∘ Q = uncurry spin ∘ fun x => (x.2 • a, mat (U x.1)) := by funext x i; exact G.mat_mul ..
    have hQ : ContDiff ℝ ω (mat ∘ Q) := by
      rw [hm]; exact spin_diff.comp ((contDiff_snd.smul contDiff_const).prodMk (h.comp contDiff_fst))
    have hf := ih Q hQ (by simpa [Q] using hz)
    rw [List.length_cons, ← Nat.sub_sub]; change FlatAt _ (fun x => deriv _ 0) _
    refine hf.partial_zero ?_
    rw [← List.ofFn_get l]
    exact (strokes_diff J l.length).comp (contDiff_const.prodMk hQ)

theorem reconstruct_strokes (U : Group G) (l : List (Dir G)) : FlatAt (J+1-l.length) (strokes J l ∘ reconstruct (mat U)) 0 := by
  let V (x : G.Color) (i : Fin 4) := if i=0 then G.lieExp x * U 3 * U 2 * (U 1)⁻¹ else U i
  have he : reconstruct (mat U) = mat ∘ V := by
    ext1 x; ext1 i
    dsimp only [reconstruct,comp_apply,mat,V]; split <;> simp [*,G.mat_mul,G.mat_inv]
  rw [he]
  refine strokes_flat J l V (he ▸ reconstruct_diff.comp (contDiff_const.prodMk contDiff_id)) ?_
  simp [V,read,mul_assoc]

lemma unscaled_tail (G : Gauge) (k : ℕ) (r : ℝ) : ∃ c : ℝ, 0 < c ∧
    ∀ (a : Fin k → Dir G), ‖a‖ ≤ r → ∀ (U : Group G) (x : G.Color), ‖x‖ ≤ 1 → G.lieExp x = read U →
      ‖strokes J (List.ofFn a) (mat U)‖ ≤ c*‖x‖^(J+1-k) := by
  let L (p : (Fin k → Dir G) × Space G) (x : G.Color) := strokes J (List.ofFn p.1) (reconstruct p.2 x)
  have hd : ContDiff ℝ ω (uncurry L) := (strokes_diff J k).comp (contDiff_fst.fst.prodMk (reconstruct_diff.comp
    (contDiff_fst.snd.prodMk contDiff_snd)))
  let K : Set ((Fin k → Dir G) × Space G) := Metric.closedBall 0 r ×ˢ Set.range mat
  obtain ⟨C,hC,he⟩ := uniform_flat_price K ((isCompact_closedBall _ _).prod (isCompact_range (f:=mat) (by unfold mat; fun_prop)))
    1 L hd (fun _ => True) (J+1-k) (by
      rintro ⟨a,W⟩ ⟨-,u,hu⟩ -
      change mat u = W at hu
      subst W
      simpa only [L,List.length_ofFn,Function.comp_def] using reconstruct_strokes J u (List.ofFn a))
  refine ⟨C,hC, fun a ha U x hx hz => ?_⟩
  have h := he (a,mat U) ⟨by simpa using ha,Set.mem_range_self U⟩ trivial x hx
  simpa only [L,reconstructed U hz] using! h

lemma small_tail (G : Gauge) (k : ℕ) (r : ℝ) : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧
    ∀ (U : Group G) (a : Fin k → Dir G) (t : ℝ), 0 < t → t ≤ δ → ‖a‖ ≤ t*r → G.chord (read U) ≤ t →
      ‖strokes J (List.ofFn a) (mat U)‖ ≤ C*t^(J+1) := by
  obtain ⟨c,b,hc,hb,h⟩ := log_chart_cost G
  obtain ⟨p,hp,h'⟩ := unscaled_tail J G k r
  let δ := min (min b c⁻¹) 1
  refine ⟨p*c^(J+1-k),δ, by positivity, lt_min (lt_min hb (inv_pos.mpr hc)) one_pos, min_le_right ..,?_⟩
  intro U a t ht ht' ha hu
  have hs := le_min_iff.mp ht'
  obtain ⟨h₁,h₂⟩ := le_min_iff.mp hs.1
  have hl := h (read U) (hu.trans h₁)
  have hx := hl.2.trans (mul_le_mul_of_nonneg_left hu hc.le)
  have hy : ‖t⁻¹ • a‖ ≤ r := by
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr ht).le]
    exact (mul_le_mul_of_nonneg_left ha (inv_pos.mpr ht).le).trans_eq (inv_mul_cancel_left₀ ht.ne' _)
  have hp' := h' (t⁻¹ • a) hy U _ (hx.trans ((mul_le_mul_of_nonneg_left h₂ hc.le).trans_eq (mul_inv_cancel₀ hc.ne'))) hl.1
  have he := strokes_smul J t (List.ofFn (t⁻¹ • a)) (mat U)
  simp only [List.length_ofFn,List.map_ofFn,comp_def,Pi.smul_apply,smul_smul,mul_inv_cancel₀ ht.ne',one_smul] at he
  rw [he,norm_mul,Real.norm_of_nonneg (pow_pos ht _).le]
  refine (mul_le_mul_of_nonneg_left (hp'.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _) hp.le))
    (pow_nonneg ht.le _)).trans ?_
  rw [mul_pow, show t^k * (p*(c^(J+1-k)*t^(J+1-k))) = p*c^(J+1-k)*t^(k+(J+1-k)) by rw [pow_add]; ring]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht.le hs.2 (by omega)) (by positivity)
end Quad
end YM.WilsonStartup
