import YM.Extra.WILSON_STARTUP.Face
/-!
# Arbitrary vanishing order curvature packets (generalizes Residual/Face)

Throughout use actual small-plaquette (not link) quantitative chart of top
prep. One can price individual homogeneous analytic coefficients, so not
only smallness of output jets.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Quad.Rose
open Function Filter Work Tensor Next.Fluctuations Lattice Wilson RG
open scoped ContDiff Topology Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n : Side}

structure Berry (G:Gauge) (k:ℕ) where
  f : G.El→ℝ
  matP : G.Mat→ℝ
  smooth : ContDiff ℝ ω matP
  actual u: matP (G.mat u)= f u
  calm {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (u:E→ G.El) (h:u 0=1)
       (hm:ContDiffAt ℝ ω (fun v=> G.mat (u v)) 0): FlatAt k (f ∘ u) 0
  conjugate u v: f (u*v*u⁻¹)=f v
  inv v: f v⁻¹=f v
namespace Berry
variable {θ:ℕ} (B:Berry G θ)

def spray : List (Dir G) → Space G → ℝ
  | [] => B.matP ∘ readMat
  | a :: l => fun X => deriv (fun t : ℝ => spray l (spin (t • a) X)) 0

theorem jet_diff (k : ℕ) : ContDiff ℝ ω fun p : (Fin k → Dir G) × Space G => spray B (List.ofFn p.1) p.2 := by
  induction k with
  | zero =>
    simp only [List.ofFn_zero, spray]
    exact (B.smooth.comp readMat_diff).comp contDiff_snd
  | succ k ih =>
    let V (p : (Fin (k+1) → Dir G) × Space G) (s : ℝ) := spray B (List.ofFn (Fin.tail p.1)) (spin (s • p.1 0) p.2)
    have ht : ContDiff ℝ ω (uncurry V) := by
      exact ih.comp ((contDiff_pi.mpr fun i => (contDiff_apply ..).comp contDiff_fst.fst).prodMk
        (spin_diff.comp ((contDiff_snd.smul ((contDiff_apply ..).comp contDiff_fst.fst)).prodMk contDiff_fst.snd)))
    simp only [List.ofFn_succ,spray, deriv]
    exact (ht.fderiv (g:=fun _ => 0) contDiff_const le_top).clm_apply (g:=fun _ => (1:ℝ)) contDiff_const

theorem jet_smul (r : ℝ) (l : List (Dir G)) (X : Space G) :
    spray B (l.map (fun a => r • a)) X = r^l.length * spray B l X := by
  induction l generalizing X with
  | nil => simp [spray]
  | cons a l ih =>
    simp only [List.map_cons, spray, List.length_cons, ih, smul_smul, mul_comm _ r,
      deriv_const_mul_field, deriv_comp_mul_left r (fun t => spray B l (spin (t • a) X)),mul_zero,smul_eq_mul,pow_succ,mul_assoc]
    ring

/-- Each differentiation can reduce the vanishing order by at most one along any
smooth family of actual links with base curvature element identity (not merely k=0). -/
theorem jet_flat (l : List (Dir G)) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E → Group G) (h : ContDiff ℝ ω (mat ∘ U)) (hz : read (U 0) = 1) :
    FlatAt (θ-l.length) (spray B l ∘ mat ∘ U) 0 := by
  induction l generalizing E with
  | nil =>
    rw [show spray B ([]:List (Dir G)) ∘ mat ∘ U = B.f ∘ read ∘ U from funext fun x => by simp only [spray,comp_apply,read_actual,B.actual]]
    simp only [List.length_nil, Nat.sub_zero]; exact B.calm _ hz (by
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
    exact (jet_diff B l.length).comp (contDiff_const.prodMk hQ)

theorem reconstruct_flat (U : Group G) (l : List (Dir G)) : FlatAt (θ-l.length) (spray B l ∘ reconstruct (mat U)) 0 := by
  let V (x : G.Color) (i : Fin 4) := if i=0 then G.lieExp x * U 3 * U 2 * (U 1)⁻¹ else U i
  have he : reconstruct (mat U) = mat ∘ V := by
    ext1 x; ext1 i
    dsimp only [reconstruct,comp_apply,mat,V]; split <;> simp [*,G.mat_mul,G.mat_inv]
  rw [he]
  refine jet_flat B l V (he ▸ reconstruct_diff.comp (contDiff_const.prodMk contDiff_id)) ?_
  simp [V,read,mul_assoc]

lemma unscaled_bound (k : ℕ) (r : ℝ) : ∃ c : ℝ, 0 < c ∧
    ∀ (a : Fin k → Dir G), ‖a‖ ≤ r → ∀ (U : Group G) (x : G.Color), ‖x‖ ≤ 1 → G.lieExp x = read U →
      ‖spray B (List.ofFn a) (mat U)‖ ≤ c*‖x‖^(θ-k) := by
  let L (p : (Fin k → Dir G) × Space G) (x : G.Color) := spray B (List.ofFn p.1) (reconstruct p.2 x)
  have hd : ContDiff ℝ ω (uncurry L) := (jet_diff B k).comp (contDiff_fst.fst.prodMk (reconstruct_diff.comp
    (contDiff_fst.snd.prodMk contDiff_snd)))
  let K : Set ((Fin k → Dir G) × Space G) := Metric.closedBall 0 r ×ˢ Set.range mat
  obtain ⟨C,hC,he⟩ := uniform_flat_price K ((isCompact_closedBall _ _).prod (isCompact_range (f:=mat) (by unfold mat; fun_prop)))
    1 L hd (fun _ => True) (θ-k) (by
      rintro ⟨a,W⟩ ⟨-,u,hu⟩ -
      change mat u = W at hu
      subst W
      simpa only [L,List.length_ofFn,Function.comp_def] using reconstruct_flat B u (List.ofFn a))
  refine ⟨C,hC, fun a ha U x hx hz => ?_⟩
  have h := he (a,mat U) ⟨by simpa using ha,Set.mem_range_self U⟩ trivial x hx
  simpa only [L,reconstructed U hz] using! h

lemma small_jet (k : ℕ) (r : ℝ) : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧
    ∀ (U : Group G) (a : Fin k → Dir G) (t : ℝ), 0 < t → t ≤ δ → ‖a‖ ≤ t*r → G.chord (read U) ≤ t →
      ‖spray B (List.ofFn a) (mat U)‖ ≤ C*t^θ := by
  obtain ⟨c,b,hc,hb,h⟩ := log_chart_cost G
  obtain ⟨p,hp,h'⟩ := unscaled_bound B k r
  let δ := min (min b c⁻¹) 1
  refine ⟨p*c^(θ-k),δ, by positivity, lt_min (lt_min hb (inv_pos.mpr hc)) one_pos, min_le_right ..,?_⟩
  intro U a t ht ht' ha hu
  have hs := le_min_iff.mp ht'
  obtain ⟨h₁,h₂⟩ := le_min_iff.mp hs.1
  have hl := h (read U) (hu.trans h₁)
  have hx := hl.2.trans (mul_le_mul_of_nonneg_left hu hc.le)
  have hy : ‖t⁻¹ • a‖ ≤ r := by
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr ht).le]
    exact (mul_le_mul_of_nonneg_left ha (inv_pos.mpr ht).le).trans_eq (inv_mul_cancel_left₀ ht.ne' _)
  have hp' := h' (t⁻¹ • a) hy U _ (hx.trans ((mul_le_mul_of_nonneg_left h₂ hc.le).trans_eq (mul_inv_cancel₀ hc.ne'))) hl.1
  have he := jet_smul B t (List.ofFn (t⁻¹ • a)) (mat U)
  simp only [List.length_ofFn,List.map_ofFn,comp_def,Pi.smul_apply,smul_smul,mul_inv_cancel₀ ht.ne',one_smul] at he
  rw [he,norm_mul,Real.norm_of_nonneg (pow_pos ht _).le]
  refine (mul_le_mul_of_nonneg_left (hp'.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _) hp.le))
    (pow_nonneg ht.le _)).trans ?_
  rw [mul_pow, show t^k * (p*(c^(θ-k)*t^(θ-k))) = p*c^(θ-k)*t^(k+(θ-k)) by rw [pow_add]; ring]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht.le hs.2 (by omega)) (by positivity)

def bud (p:Cell n) (U: Config G n) := B.f (faceValue U p)

theorem bud_jet (p : Cell n) (U : Config G n) (l : List (Directions G n)) :
    leftDerivs (bud B p) l U = spray B (l.map (· ∘ edges p)) (Quad.mat (U ∘ edges p)) := by
  induction l generalizing U with
  | nil => rw [leftDerivs, List.map_nil, spray, comp_apply, Quad.read_actual, B.actual, read_edges]; rfl
  | cons a l ih =>
    simp only [leftDerivs, List.map_cons, ih, spray]
    exact congr_arg (deriv · 0) (funext fun t => congr_arg _ (funext fun i : Fin 4 => G.mat_mul ..))

theorem bud_price (k P : ℕ) : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧
    ∀ (b : BudgetPoint), b.power = P → b.order = k → b.threshold ≤ δ → ∀ (n : Side) (p : Cell n) (o : Site n),
      o ∈ touched p → b.supBounds o (touched p) (bud B p) (C*b.threshold^θ) := by
  let J := Fin (k+1)
  choose c d hc hd h' h using fun i : J => small_jet B i.val ((1+4)^P)
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
  rw [bud_jet, ← show List.ofFn a = l.map (· ∘ edges p) from (List.map_ofFn (g:=(· ∘ edges p)) (f:=l.get)).symm.trans (by rw [List.ofFn_get])]
  exact H.trans (mul_le_mul_of_nonneg_right hcj (pow_nonneg b.threshold_pos.le _))

theorem bud_smooth (p : Cell n) (U : Config G n) : ContDiff ℝ ω (bud B p ∘ increment U) := by
  simp_rw [comp_def, bud, ← B.actual]
  exact B.smooth.comp (mat_face_inc ..)

theorem bud_regular (p : Cell n) (b : BudgetPoint) : b.Regular (touched p) (bud B p) := by
  have h (U : Config G n) := ((bud_smooth B p U).of_le (m:=(b.order:ℕ∞)) le_top).contDiffAt (x:=0)
  refine ⟨fun U V h => congr_arg B.f (face_local p U V h), Continuous.measurable ?_, ?_,fun U _ => h U,
    fun U _ a l hl => Next.Foundations.left_has a hl (h U)⟩
  · change Continuous fun U => bud B p U
    simp only [bud,← B.actual]; exact B.smooth.continuous.comp
      (G.continuous_mat.comp (continuous_travel ..))
  intro k U; exact (congr_arg B.f (face_gauge k U p)).trans (B.conjugate ..)

theorem bud_flat (p : Cell n) : FlatAt θ (bud B p ∘ increment 1) 0 := by
  refine B.calm (fun v => faceValue (increment 1 v) p) ?_ (mat_face_inc .. |>.contDiffAt)
  rw [Work.G07.at_zero_increment,face_one]

theorem bud_one (h₁: 0 < θ) (p : Cell n) : bud B p 1 = 0 := by
  have h := congr_arg (Tensor.diagonal · (0:Directions G n)) (bud_flat B p 0 (by omega))
  simpa [Tensor.diagonal,comp_def,G07.at_zero_increment] using! h

theorem bud_hess (h₂: 2<θ) (p : Cell n) (x y : Directions G n) : logHessian (bud B p) x y = 0 :=
  congr_arg (fun u : Tensor.T (Directions G n) ℝ 2 => u ![x,y]) (bud_flat B p 2 (by omega))

theorem bud_send (p : Cell n) (s : Signed) (x : Site n) (U : Config G n) :
    bud B (Face.send s x p) U = bud B p (pull s x U) :=
  (Face.send_price U p s x B.f B.inv (fun v u => B.conjugate u v)).symm
end Berry
end YM.WilsonStartup.Quad.Rose
