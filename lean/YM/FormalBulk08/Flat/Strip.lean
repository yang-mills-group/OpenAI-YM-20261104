import YM.FormalBulk08.Flat.Pairs
import Mathlib.Analysis.Real.Pi.Bounds

/-! Avoid quantitative complex pole arithmetic. Consume a fixed-powers real
puncture estimate and retain genuine exponential costs in an interior of the
**same** width; this is important for not hiding `L` in a claimed pre-block
width. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Precision RG Next.Free UVExtension.Free Work.F08
open scoped Topology BigOperators

lemma mode_move (p : Momentum) (hp : physical p) (x : Cover) :
    ‖mode p x-mode 0 x‖ ≤ ‖p‖*Laurent.size x := by
  rw [mode_constant]
  unfold mode
  let z : ℂ := ∑ i,p i*(x i)
  have he : z.im=0 := by
    unfold z; rw [Complex.im_sum]
    simp [(physical_iff p).1 hp,Complex.mul_im]
  apply (real_chip z he).trans
  unfold z Laurent.size; push_cast
  apply (norm_sum_le ..).trans; rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _=> ?_
  rw [norm_mul,Complex.norm_intCast,abs_nat]
  exact mul_le_mul_of_nonneg_right (norm_le_pi_norm _ _) (by positivity)

lemma series_origin (f : Cover → ℝ) (σ E : ℝ) (hp : 0<σ) (h : Laurent.Width σ E f)
    (p : Momentum) (hv : physical p) :
    ‖RRead f p-RRead f 0‖≤ E/σ*‖p‖ := by
  have hx := (h.unweighted hp.le).2.1
  let a (i : Cover) := mode p i*(f i:ℂ)
  let b (i : Cover) := mode 0 i*(f i:ℂ)
  let t (i : Cover) := Real.exp (σ*Laurent.size i)*‖f i‖
  have ha : Summable a := real_series hx hv; have hb : Summable b:=real_series hx (by simp [physical])
  have he (i : Cover) : ‖a i-b i‖ ≤ t i * (‖p‖/σ) := by
    have hh : (Laurent.size i:ℝ) ≤ Real.exp (σ*Laurent.size i)/σ :=
      (le_div_iff₀ hp).mpr (by linarith only [Real.add_one_le_exp (σ*Laurent.size i)])
    unfold a b t; rw [← sub_mul,norm_mul,Complex.norm_real]
    exact (mul_le_mul_of_nonneg_right ((mode_move p hv i).trans (mul_le_mul_of_nonneg_left hh (norm_nonneg _))) (norm_nonneg _)).trans_eq (by ring)
  change ‖(∑' i,a i)-∑' i,b i‖ ≤ _
  have ht : Summable fun i=> t i*(‖p‖/σ) := h.2.1.mul_right _
  have hs := ht.of_nonneg_of_le (fun i => norm_nonneg _) he
  rw [← ha.tsum_sub hb]; apply (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum he ht).trans ?_)
  rw [tsum_mul_right]; exact (mul_le_mul_of_nonneg_right h.2.2 (by positivity)).trans_eq (by ring)

lemma catalogue (f : Cover → ℝ) (h : Summable fun x=> ‖f x‖) (B : ℝ) (hc : ∀ p∈baseCube, ‖RRead f p‖ ≤ B) (x : Cover) : ‖f x‖ ≤ B := by
  let A : Row Unit Unit := fun _ _=> f
  have ha : A.safe:= fun _ _=> h
  have he (n : Side) (y : Site n) :
      (((n.val:ℂ)^4) • approached (A.acts n)) (0,()) (y,()) = ∑ p : Site n, RRead f (mon p)*star (cell p y) := by
    rw [← Matrix.mul_one (approached (A.acts n)), ← Matrix.mul_smul, ← rotations_gram, ← Matrix.mul_assoc,circulant n _ ha,
      Matrix.mul_apply,Fintype.sum_prod_type]
    simp only [Fintype.sum_unique, rot_fiber,cell_origin,one_mul]
    congr
  have hh (n : Side) (y : Site n) : ‖A.acts n (0,()) (y,())‖ ≤ B := by
    have hw : 0 < (n.val:ℝ)^4:=pow_pos (side_pos _) _
    apply le_of_mul_le_mul_left _ hw
    calc
      _ = ‖(((n.val:ℂ)^4) • approached (A.acts n)) (0,()) (y,())‖ := by simp [approached]
      _ ≤ _ := by
        rw [he]; apply (norm_sum_le ..).trans
        calc
          _ ≤ ∑ _ : Site n,B := Finset.sum_le_sum fun i _=> by
            rw [norm_mul,norm_star,show ‖cell i y‖=1 from mode_real _ _ (mon_mem _ _).1,mul_one]
            exact hc _ (mon_mem n _)
          _ = (n.val:ℝ)^4*B := by simp only [Finset.sum_const,Finset.card_univ,site_card,nsmul_eq_mul]; norm_cast
  let n (i : ℕ) : Side := ⟨i+1,Nat.succ_pos _⟩
  have ht : Tendsto (fun i=> (n i).val) atTop atTop:= tendsto_add_atTop_nat _
  exact le_of_tendsto (entry_limit n ht A ha () () x).norm (Eventually.of_forall fun i=> hh _ _)

lemma peak_read (f : Cover→ℝ) {σ E C X : ℝ} (hp : 0<σ) (hE : 0≤E) (hC : 0≤C) (hX : 0<X) (hx : X≤1)
    (n : ℕ) (h : Laurent.Width σ E f)
    (hk : ∀ p∈baseCube, p≠0 → ‖RRead f p‖ ≤ C*(domainRadius/‖p‖)^n * X^(n+1)) :
    ∀ p ∈ baseCube, ‖RRead f p‖ ≤ (C*domainRadius^n+2*(E/σ))*X := by
  have hS p (hp : p∈baseCube) (he : X ≤ ‖p‖) : ‖RRead f p‖ ≤ C*domainRadius^n*X := by
    apply (hk _ hp (norm_pos_iff.mp (hX.trans_le he))).trans
    have hb := domainRadius_pos
    calc
      _ ≤ C*(domainRadius/X)^n*X^(n+1) := by gcongr
      _ = _ := by rw [div_pow,pow_succ]; field_simp
  let y : Momentum:=fun _=>(X:ℂ); have he : ‖y‖=X := by simp [y,Real.norm_of_nonneg hX.le]
  have hy : y∈baseCube := by
    constructor; · ext; simp [y]
    intro i; simp only [y,Complex.ofReal_re, abs_of_pos hX]; linarith only [hx,Real.pi_gt_three]
  have hz := hS y hy he.ge
  have hd := series_origin f σ E hp h y hy.1; rw [he,norm_sub_rev] at hd
  intro p hs; by_cases ht : X≤‖p‖
  · exact (hS p hs ht).trans (by gcongr; apply le_add_of_nonneg_right; positivity)
  have hh : E/σ*‖p‖≤ E/σ*X:= by gcongr; exact le_of_not_ge ht
  exact ((norm_le_norm_sub_add _ (RRead f 0)).trans
    (add_le_add ((series_origin f _ _ hp h p hs.1).trans hh) ((norm_le_norm_sub_add _ (RRead f y)).trans (add_le_add hd hz)))).trans_eq (by ring)

lemma releasing (f : Cover→ℝ) {σ E B : ℝ} (hp : 0<σ) (h : Laurent.Width σ E f)
    (hE : 0 ≤ E) (hb : ∀ x, ‖f x‖ ≤ B) :
    let s:=σ/4
    Laurent.Width s ((2*((1+s)/s))^4*Real.sqrt (E*B)) f := by
  intro s
  have hs : 0<s:=by unfold s; positivity
  let D:=Real.sqrt (E*B)
  have H x : Real.exp (s*Laurent.size x)*‖f x‖ ≤ Real.exp (-s*Laurent.size x)*D := by
    have he : Real.exp (σ*Laurent.size x)*‖f x‖ ≤ E :=
      (h.2.1.le_tsum x (fun _ _=> by positivity)).trans h.2.2

    have hy : Real.exp (2*s*Laurent.size x)*‖f x‖ ≤ D := by
      apply Real.le_sqrt_of_sq_le
      calc
        _ = (Real.exp (σ*Laurent.size x)*‖f x‖)*‖f x‖ := by
          rw [mul_pow,← Real.exp_nat_mul]; unfold s; norm_num; ring_nf; rw [sq_abs]
        _ ≤ _ := mul_le_mul he (hb x) (norm_nonneg _) hE
    have ht := mul_le_mul_of_nonneg_left hy (Real.exp_pos (-s*Laurent.size x)).le
    refine le_trans (le_of_eq ?_) ht
    rw [← mul_assoc, ← Real.exp_add,show -s*Laurent.size x+2*s*Laurent.size x=s*Laurent.size x by ring]
  have hh := Laurent.Width.compactPay (α:=Axis) s hs
  have hv := hh.2.1.mul_right D
  have hb x : 0≤Real.exp (s*Laurent.size x)*‖f x‖ := by positivity
  have hu := hv.of_nonneg_of_le hb H
  refine ⟨hb,hu,(hu.tsum_le_tsum H hv).trans ?_⟩
  rw [tsum_mul_right]
  exact mul_le_mul_of_nonneg_right (by simpa only [Axis,Fintype.card_fin] using hh.2.2) (Real.sqrt_nonneg _)

theorem strip_from_real (σ E C : ℝ) (h : 0<σ) (hE : 0<E) (hC : 0<C) (n : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀ f g : Cover→ℝ, Laurent.Width σ E f → Laurent.Width σ E g →
      ∀ X : ℝ, 0<X → X≤1 → (∀ p∈baseCube, p≠0 → ‖RRead f p-RRead g p‖≤ C*(domainRadius/‖p‖)^n*X^(n+1)) →
        Laurent.Width (σ/4) (K*Real.sqrt X) (fun x=> f x-g x) := by
  let s:=σ/4
  let B:= C*domainRadius^n+2*((E+E)/σ)
  have hs : 0<s:=by unfold s; positivity
  have hB : 0<B:= by unfold B; have := domainRadius_pos; positivity
  refine ⟨(2*((1+s)/s))^4 * Real.sqrt ((E+E)*B),by positivity,fun f g hf hg X hX hx he=>?_⟩
  let v := fun x=>f x-g x
  have hh : Laurent.Width σ (E+E) v := strip_minus (P:=fun _ : Unit => fun _ : Unit => f) (R:=fun (_ : Unit) (_ : Unit) => g) (fun _ _=>hf) (fun _ _=>hg) () ()
  have hz : ∀ p∈baseCube, ‖RRead v p‖≤B*X := peak_read v h (add_nonneg hE.le hE.le) hC.le hX hx n hh (fun p hp hn => by
    rw [show RRead v p = _ from (market_sub (hf.unweighted h.le).2.1 (hg.unweighted h.le).2.1 p hp.1)]; exact he _ hp hn)
  have hl:= releasing v h hh (add_nonneg hE.le hE.le) (catalogue v (hh.unweighted h.le).2.1 _ hz)
  apply hl.mono le_rfl
  apply le_of_eq
  rw [← mul_assoc (E+E),Real.sqrt_mul (mul_pos (add_pos hE hE) hB).le]; ring
end YM.FormalBulk08.Flat
