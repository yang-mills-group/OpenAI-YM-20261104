import YM.Extra.WILSON_STARTUP.Face

/-!
# Startup recurrence at arbitrary fixed Taylor order (local)

Strengthens WilsonStartup's Quad proof to the entire Wilson input in the
shared curvature convention. `predict` uses coefficients of the Wilson
unmasked one-plaquette germ, not of the pushed/assembled answer. Order P
in fluctuation units with actual β = g^{-2} requires degree P+2 here.
`lag_price` pays P+3 zeros WITH mixed EBound left derivatives (even when
those derivatives outnumber the rank); volume-uniform, wraps OK; evaluation
before masking, cancellation only on identical labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG04B.Startup
open Function Filter Work Tensor RG Wilson Lattice
open WilsonStartup WilsonStartup.Quad
open scoped ContDiff Topology Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge}

def predict (G : Gauge) (e : ℕ) := G05.blockTaylor e (inK G)
def later (d : ℕ) (u : G.El) := G.price u - predict G d (G.curvature u)

lemma correct_four (u : G.El) : later 4 u = surplus u := by simp only [later, predict, surplus, convert_taylor]; ring

lemma predicts (i : ℕ) (x : G.Color) : predict G (i+1) x = predict G i x + diagonal (coeff (inK G) (i+1) 0) x := by
  unfold predict G05.blockTaylor
  rw [Finset.sum_range_succ]
  rfl

lemma local_later (j : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : E → G.El)
    (h : u 0=1) (hm : ContDiffAt ℝ ω (fun v=> G.mat (u v)) 0) : FlatAt (j+1) (later j ∘ u) 0 := by
  have hc : ContinuousAt u 0 := (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.continuousAt_iff.mpr hm.continuousAt
  let k x:= G.curvature (u x)
  have hz:k 0 = 0 := by simp only [k,h,G.curvature_unit]
  refine FlatAt.congr (g:=later j ∘ u) (FlatAt.comp (f:=inK G-G05.blockTaylor j (inK G)) (u:=k)
    (hz.symm ▸ flat_sub_taylor _ _ (inK_diff.of_le le_top)) (by rw [hz]; exact (inK_diff.of_le le_top).sub (G05.blockTaylor_contDiff ..|>.contDiffAt)) ((Next.Fluctuations.curvature_diff_mat u 0 hm).of_le le_top)) ?_
  filter_upwards [(show Tendsto u (𝓝 0) (𝓝 1) from h ▸ hc.tendsto).eventually (recover_left G)] with x hx
  simp only [comp_apply,Pi.sub_apply,k,predict,inK,hx,later]

def tailMat (e : ℕ) (X : G.Mat) := Quad.distMat X - predict G e (Quad.kMat X)
lemma onMat (e : ℕ) (u : G.El) : tailMat e (G.mat u) = later e u := by
  rw [tailMat,Quad.k_actual,later,Quad.distMat,← div_pow]
  change G.chord u ^ 2 / 2 - _ = _
  rw [G.chord_price]; ring

lemma mat_cont (j : ℕ) : ContDiff ℝ ω (tailMat j (G:=G)) := by
  have he : ContDiff ℝ ω (Quad.distMat (G:=G)) := (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const _).div_const _
  exact he.sub ((G05.blockTaylor_contDiff ..).comp Quad.kMat_diff)

-- Four physical links, all left increments

def monitor (i : ℕ) : List (Quad.Dir G) → Quad.Space G → ℝ
  | [] => tailMat i ∘ Quad.readMat
  | a :: l => fun X => deriv (fun t : ℝ => monitor i l (spin (t • a) X)) 0

lemma monitor_diff (j k : ℕ) : ContDiff ℝ ω fun p : (Fin k → Quad.Dir G) × Quad.Space G => monitor j (List.ofFn p.1) p.2 := by
  induction k with
  | zero =>
    simp only [List.ofFn_zero, monitor]
    exact ((mat_cont j).comp readMat_diff).comp contDiff_snd
  | succ k ih =>
    let V (p : (Fin (k+1) → Quad.Dir G) × Quad.Space G) (s : ℝ) := monitor j (List.ofFn (Fin.tail p.1)) (spin (s • p.1 0) p.2)
    have ht : ContDiff ℝ ω (uncurry V) := by
      exact ih.comp ((contDiff_pi.mpr fun i => (contDiff_apply ..).comp contDiff_fst.fst).prodMk
        (spin_diff.comp ((contDiff_snd.smul ((contDiff_apply ..).comp contDiff_fst.fst)).prodMk contDiff_fst.snd)))
    simp only [List.ofFn_succ,monitor,deriv]
    exact (ht.fderiv (g:=fun _ => 0) contDiff_const le_top).clm_apply (g:=fun _ => (1:ℝ)) contDiff_const

lemma tally (j : ℕ) (r : ℝ) (l : List (Quad.Dir G)) (X : Quad.Space G) :
    monitor j (l.map (fun a=> r • a)) X = r^l.length * monitor j l X := by
  induction l generalizing X with
  | nil => simp [monitor]
  | cons a l ih =>
    simp only [List.map_cons,monitor,List.length_cons,ih,smul_smul, mul_comm _ r,
      deriv_const_mul_field, deriv_comp_mul_left r (fun t => monitor j l (spin (t • a) X)),mul_zero,smul_eq_mul,pow_succ,mul_assoc]
    ring

lemma vanish (j : ℕ) (l : List (Quad.Dir G)) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E → Quad.Group G) (h : ContDiff ℝ ω (Quad.mat ∘ U)) (hz : Quad.read (U 0)=1) :
    FlatAt (j+1-l.length) (monitor j l ∘ Quad.mat ∘ U) 0 := by
  induction l generalizing E with
  | nil =>
    rw [show monitor j ([]:List (Quad.Dir G)) ∘ Quad.mat ∘ U=later j ∘ Quad.read ∘ U from
      funext fun x=> by simp only [monitor,comp_apply,read_actual,onMat]]
    exact local_later j _ hz (by simp only [comp_apply,← read_actual]; exact (readMat_diff.comp h).contDiffAt)
  | cons x l ih =>
    let Q (v:E × ℝ) (i:Fin 4) := G.lieExp (v.2 • x i)*U v.1 i
    have hm : Quad.mat ∘ Q=uncurry spin ∘ fun v => (v.2 • x, Quad.mat (U v.1)) := by funext v i; exact G.mat_mul ..
    have hQ : ContDiff ℝ ω (Quad.mat ∘ Q) := by rw [hm]; exact spin_diff.comp ((contDiff_snd.smul contDiff_const).prodMk (h.comp contDiff_fst))
    have hf := ih Q hQ (by simpa [Q] using hz)
    rw [List.length_cons,← Nat.sub_sub]; change FlatAt _ (fun y=> deriv _ 0) _
    refine hf.partial_zero ?_
    rw [← List.ofFn_get l]; exact (monitor_diff j l.length).comp (contDiff_const.prodMk hQ)

lemma contour (U : Quad.Group G) (j : ℕ) (l : List (Quad.Dir G)) :
    FlatAt (j+1-l.length) (monitor j l ∘ reconstruct (Quad.mat U)) 0 := by
  let V (x:G.Color) (i:Fin 4):= if i=0 then G.lieExp x * U 3 * U 2 * (U 1)⁻¹ else U i
  have he: reconstruct (Quad.mat U) = Quad.mat ∘ V:= by
    ext1 x; ext1 i; dsimp only [reconstruct,comp_apply,Quad.mat,V]; split <;> simp [*,G.mat_mul,G.mat_inv]
  rw [he]
  refine vanish j l V (he ▸ reconstruct_diff.comp (contDiff_const.prodMk contDiff_id)) ?_
  simp [V,Quad.read,mul_assoc]

private lemma preliminary (G : Gauge) (j k : ℕ) (r : ℝ) : ∃ c : ℝ, 0 < c ∧
    ∀ (a : Fin k → Quad.Dir G), ‖a‖ ≤ r → ∀ (U : Quad.Group G) (x : G.Color), ‖x‖ ≤ 1 → G.lieExp x = Quad.read U →
      ‖monitor j (List.ofFn a) (Quad.mat U)‖ ≤ c*‖x‖^(j+1-k) := by
  let F (p : (Fin k → Quad.Dir G) × Quad.Space G) (x : G.Color) := monitor j (List.ofFn p.1) (reconstruct p.2 x)
  have hf : ContDiff ℝ ω (uncurry F) := (monitor_diff j k).comp (contDiff_fst.fst.prodMk (reconstruct_diff.comp (contDiff_fst.snd.prodMk contDiff_snd)))
  let K : Set ((Fin k → Quad.Dir G) × Quad.Space G) := Metric.closedBall 0 r ×ˢ Set.range Quad.mat
  obtain ⟨C,hC,he⟩ := uniform_flat_price K ((isCompact_closedBall _ _).prod (isCompact_range (f:=Quad.mat) (by unfold Quad.mat; fun_prop)))
    1 F hf (fun _=> True) (j+1-k) (by
      rintro ⟨a,W⟩ ⟨-,u,hu⟩ -; change Quad.mat u = W at hu; subst W
      simpa only [F,List.length_ofFn,Function.comp_def] using contour u j (List.ofFn a))
  refine ⟨C,hC, fun a ha U x hx hz=>?_⟩
  have h:= he (a,Quad.mat U) ⟨by simpa using ha, Set.mem_range_self U⟩ trivial x hx
  simpa only [F,reconstructed U hz] using! h

private lemma weight (G : Gauge) (j k : ℕ) (r : ℝ) : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧
    ∀ (U : Quad.Group G) (a : Fin k → Quad.Dir G) (t : ℝ), 0 < t → t ≤ δ → ‖a‖ ≤ t*r → G.chord (Quad.read U) ≤ t →
      ‖monitor j (List.ofFn a) (Quad.mat U)‖ ≤ C*t^(j+1) := by
  obtain ⟨c,b,hc,hb,h⟩ := Next.Fluctuations.log_chart_cost G
  obtain ⟨p,hp,h'⟩ := preliminary G j k r
  let δ := min (min b c⁻¹) 1
  refine ⟨p*c^(j+1-k),δ, by positivity, lt_min (lt_min hb (inv_pos.mpr hc)) one_pos, min_le_right ..,?_⟩
  intro U a t ht ht' ha hu
  have hs := le_min_iff.mp ht'
  obtain ⟨h₁,h₂⟩ := le_min_iff.mp hs.1
  have hl := h (Quad.read U) (hu.trans h₁)
  have hx := hl.2.trans (mul_le_mul_of_nonneg_left hu hc.le)
  have hy : ‖t⁻¹ • a‖ ≤ r := by
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr ht).le]
    exact (mul_le_mul_of_nonneg_left ha (inv_pos.mpr ht).le).trans_eq (inv_mul_cancel_left₀ ht.ne' _)
  have hp' := h' (t⁻¹ • a) hy U _ (hx.trans ((mul_le_mul_of_nonneg_left h₂ hc.le).trans_eq (mul_inv_cancel₀ hc.ne'))) hl.1
  have he := tally j t (List.ofFn (t⁻¹ • a)) (Quad.mat U)
  simp only [List.length_ofFn,List.map_ofFn,comp_def,Pi.smul_apply,smul_smul,mul_inv_cancel₀ ht.ne',one_smul] at he
  rw [he,norm_mul,Real.norm_of_nonneg (pow_pos ht _).le]
  refine (mul_le_mul_of_nonneg_left (hp'.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _) hp.le)) (pow_nonneg ht.le _)).trans ?_
  rw [mul_pow, show t^k*(p*(c^(j+1-k)*t^(j+1-k)))=p*c^(j+1-k)*t^(k+(j+1-k)) by rw [pow_add]; ring]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht.le hs.2 (by omega)) (by positivity)

variable {n : Side}
def lag (G : Gauge) (j : ℕ) (p : Cell n) (U : Config G n) := later j (faceValue U p)

lemma lag_smooth (j : ℕ) (p : Cell n) (U : Config G n) : ContDiff ℝ ω (lag G j p ∘ increment U) := by
  simp_rw [comp_def,lag,←onMat]; exact (mat_cont j).comp (mat_face_inc ..)

lemma vacant (j : ℕ) (p : Cell n) : FlatAt (j+1) (lag G j p ∘ increment 1) 0 :=
  local_later j _ (by rw [Work.G07.at_zero_increment,face_one]) (mat_face_inc ..|>.contDiffAt)
lemma lag_one (j : ℕ) (p : Cell n) : lag G j p 1=0 := by
  have h := congr_arg (Tensor.diagonal · (0:Directions G n)) (vacant j p 0 (Nat.zero_lt_succ _))
  simpa [Tensor.diagonal,comp_def,G07.at_zero_increment] using! h
lemma lag_hessian (j : ℕ) (p : Cell n) (h : 2 ≤ j) (x y : Directions G n) : logHessian (lag G j p) x y = 0 :=
  congr_arg (fun u : Tensor.T (Directions G n) ℝ 2 => u ![x,y]) (vacant j p 2 (by omega))

lemma lag_regular (j : ℕ) (p : Cell n) (b : BudgetPoint) : b.Regular (touched p) (lag G j p) := by
  have h (U : Config G n) := ((lag_smooth j p U).of_le (m:=(b.order:ℕ∞)) le_top).contDiffAt (x:=0)
  refine ⟨fun U V h => congr_arg (later j) (WilsonStartup.face_local p U V h), Continuous.measurable ?_,?_, fun U _ => h U,
    fun U _ a _ he => Next.Foundations.left_has a he (h U)⟩
  · change Continuous (fun U => lag G j p U)
    simp_rw [lag,← onMat]
    exact (mat_cont j).continuous.comp (G.continuous_mat.comp (continuous_travel ..))
  intro k U; unfold lag later; rw [face_gauge,G.price_conj,G.curvature_conjugate]
  congr 1
  unfold predict G05.blockTaylor; rw [_root_.Finset.sum_apply,Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _=> coeff_adjoint _ i _)

lemma markedLag (j : ℕ) (p : Cell n) (U : Config G n) (l : List (Directions G n)) :
    leftDerivs (lag G j p) l U = monitor j (l.map (· ∘ edges p)) (Quad.mat (U ∘ edges p)) := by
  induction l generalizing U with
  | nil => rw [leftDerivs,List.map_nil,monitor,comp_apply,read_actual,onMat,read_edges]; rfl
  | cons a l ih => simp only [leftDerivs,List.map_cons,ih,monitor]; exact congr_arg (deriv · 0) (funext fun t=> congr_arg _ (funext fun i : Fin 4 => G.mat_mul ..))

/-- Per-occurrence *derivative/support-point* price pre-L -/
lemma lag_price (G : Gauge) (j k P : ℕ) : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧
    ∀ (b : BudgetPoint), b.power=P → b.order=k → b.threshold ≤ δ → ∀ (n : Side) (p : Cell n) (o : Site n),
      o∈touched p → b.supBounds o (touched p) (lag G j p) (C*b.threshold^(j+1)) := by
  let J := Fin (k+1)
  choose c d hc hd h' h using fun i : J=> weight G j i.val ((1+4)^P)
  obtain ⟨i,hi,he⟩ := Finset.exists_min_image Finset.univ d Finset.univ_nonempty
  let C := 1 + ∑ m:J,c m
  have hC : 0 < C := add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _=> (hc i).le)
  refine ⟨C,d i,hC,hd i,h' i,fun b hb hk ht n p o ho=> ⟨mul_nonneg hC.le (pow_nonneg b.threshold_pos.le _),?_⟩⟩
  intro U hu l hl hA
  rw [hk] at hl
  let z:J:= ⟨l.length, Nat.lt_succ_of_le hl⟩
  let a (i : Fin z.val):= l.get i ∘ edges p
  have ha : ‖a‖ ≤ b.threshold*(1+4:ℝ)^P := by
    have hh:= b.threshold_pos
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro s
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro f
    apply ((hA _ (l.get_mem s)) (edges p f)).trans
    rw [hb]; gcongr
    exact_mod_cast (separation_triangle (edges p f).1 p.1 o).trans (Nat.add_le_add (visit_near p (edges_visit p f))
      ((separation_comm _ _) ▸ visit_near p ho))
  have H:= h z (U ∘ edges p) a _ b.threshold_pos (ht.trans (he z (Finset.mem_univ z))) ha ((read_edges p U).symm ▸ healthy_chord p U hu)
  have hZ : c z ≤ C := (Finset.single_le_sum (fun i _=> (hc i).le) (Finset.mem_univ z)).trans (le_add_of_nonneg_left zero_le_one)
  rw [markedLag,← show List.ofFn a = l.map (· ∘ edges p) from (List.map_ofFn (g:=(· ∘ edges p)) (f:=l.get)).symm.trans (by rw [List.ofFn_get])]
  exact H.trans (mul_le_mul_of_nonneg_right hZ (pow_nonneg b.threshold_pos.le _))
end YM.RG04B.Startup
