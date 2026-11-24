import YM.SchemeConversionRG11.Foundation.Inverse

/-!
# Coefficientwise parameter limits

Convergence is along a particular coupled regulator set, not interchanging evaluation and
summation. In particular inverse convergence here is of any *fixed number* of coefficients.
-/

set_option autoImplicit false
noncomputable section

namespace YM.SchemeConversionRG11.Series

open Function Filter Pert.Position Set
open scoped Topology ContDiff BigOperators

/-- Convergence through a fixed finite order. -/
def Converges {I E : Type*} [TopologicalSpace E] (n : ℕ) (l : Filter I)
    (A : I → Series E) (a : Series E) :=
  ∀ j ≤ n, Tendsto (fun i ↦ A i j) l (𝓝 (a j))

variable {E F I : Type*} {l : Filter I}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {A B : I → Series E} {a b : Series E} {X : I → Series ℝ} {x : Series ℝ} {n : ℕ}

/-- All data needed for an order-n evaluation/truncation as normed variables. -/
abbrev Window (E : Type*) (n : ℕ) := Fin (n+1) → E

def window (n : ℕ) (a : Series E) : Window E n := fun j ↦ a j

def readPoly {n : ℕ} (p : Window E n) (t : ℝ) := ∑ i, t^(i.val) • p i

@[simp] theorem poly_all (n : ℕ) (a : Series E) (t : ℝ) : readPoly (window n a) t = trunc a n t := by
  unfold trunc curve readPoly window
  rw [Finset.sum_range]

theorem poly_uncurry (n : ℕ) : ContDiff ℝ ω (uncurry (readPoly (E := E) (n := n))) := by
  unfold uncurry readPoly; fun_prop

omit [NormedSpace ℝ E] in
theorem Converges.mono (h : Converges n l A a) {p : ℕ} (hp : p ≤ n) : Converges p l A a :=
  fun j hj ↦ h j (hj.trans hp)
omit [NormedSpace ℝ E] in
theorem Converges.unique [l.NeBot] (h : Converges n l A a) (k : Converges n l A b) :
    Through n a b := fun i hi ↦ tendsto_nhds_unique (h i hi) (k i hi)
omit [NormedSpace ℝ E] in
theorem Converges.through (h : Converges n l A a) (k : ∀ᶠ i in l, Through n (A i) (B i)) :
    Converges n l B a :=
  fun i hi ↦ (h i hi).congr' (k.mono fun _ hj ↦ hj i hi)

theorem record_cont {v : E} {f : E → ℝ → F} (h : ContDiffAt ℝ ω (uncurry f) (v,0)) (p : ℕ) :
    ContinuousAt (fun u ↦ record (f u) p) v :=
  continuousAt_const.smul (partial_right _ _ h)

omit [NormedSpace ℝ E] in
theorem Converges.tend_window (h : Converges n l A a) :
    Tendsto (fun i ↦ window n (A i)) l (𝓝 (window n a)) :=
  tendsto_pi_nhds.mpr (fun j ↦ h j (Nat.le_of_lt_succ j.isLt))

theorem Converges.lift {f : E → F} (hf : ContDiffAt ℝ ω f (a 0)) (h : Converges n l A a) :
    Converges n l (fun i ↦ liftJet f (A i)) (liftJet f a) := by
  intro p hp
  have ht : ContDiffAt ℝ ω (uncurry (fun (w : Window E p) t ↦ f (readPoly w t)))
      (window p a,0) := by
    apply ContDiffAt.comp (g := f) (f := uncurry (readPoly (E := E)))
    · simpa [uncurry, trunc, curve_zero] using hf
    exact (poly_uncurry p).contDiffAt
  have he := (record_cont ht p).tendsto.comp (h.mono hp |>.tend_window)
  simpa only [comp_def, poly_all, liftJet] using he

theorem Converges.subJet (h : Converges n l A a) (k : Converges n l X x) :
    Converges n l (fun i ↦ subJet (A i) (X i)) (subJet a x) := by
  intro p hp
  have ht : ContDiffAt ℝ ω (uncurry (fun (w : Window E p × Window ℝ p) t ↦
      readPoly w.1 (readPoly w.2 t))) ((window p a, window p x), (0:ℝ)) := by
    unfold uncurry readPoly; fun_prop
  have he := (record_cont ht p).tendsto.comp
    ((h.mono hp |>.tend_window).prodMk_nhds (k.mono hp |>.tend_window))
  simpa only [comp_def, poly_all, Series.subJet] using he

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem Converges.both {C : I → Series F} {c : Series F}
    (h : Converges n l A a) (k : Converges n l C c) :
    Converges n l (fun i ↦ both (A i) (C i)) (both a c) :=
  fun j hj ↦ (h j hj).prodMk_nhds (k j hj)

section Invert
-- One chart across varying coefficients. No assumption on regulator derivative rates.
local notation "P" => Window ℝ n
private def roll (n : ℕ) (s : (Window ℝ n × ℝ) × ℝ) := readPoly s.1.1 s.2 - s.1.2

private lemma roll_smooth (n : ℕ) : ContDiff ℝ ω (roll n) := by
  unfold roll readPoly; fun_prop

private lemma roll_solve (hn : 1 ≤ n) (hg : Good x) :
    ∃ φ, Reports (roll n) (window n x, 0) 0 φ := by
  have hur := roll_smooth n
  let v : P × ℝ := (window n x,0)
  let f := trunc x n
  have hD : fderiv ℝ (roll n) (v,0) ∘L .inr ℝ (P × ℝ) ℝ = fderiv ℝ f 0 := by
    symm
    have he : f = roll n ∘ fun i ↦ (v,i) := by ext1 i; simp [roll,f,v]
    have hp : HasFDerivAt (fun i : ℝ ↦ (v,i)) (.inr ℝ (P × ℝ) ℝ) 0 :=
      (hasFDerivAt_const v (0:ℝ)).prodMk (hasFDerivAt_id (0:ℝ))
    rw [he]; exact ((hur.differentiable (by simp) _).hasFDerivAt.comp _ hp).fderiv
  apply Reports.of_square (x := v) hur.contDiffAt
  rw [hD]
  have hd : DifferentiableAt ℝ f 0 := (trunc_represents x n).regular.differentiableAt (by simp)
  have hw : deriv f 0 ≠ 0 := ((trunc_represents x n).first hn).trans_ne hg.2
  have hE (i : ℝ) : fderiv ℝ f 0 i = i * deriv f 0 := by rw [hd.hasDerivAt.hasFDerivAt.fderiv]; rfl
  have hb : Bijective (fderiv ℝ f 0) := ⟨fun y z H ↦ mul_right_cancel₀ hw (by simpa only [hE] using H),
    fun y ↦ ⟨y / deriv f 0, by rw [hE, div_mul_cancel₀ _ hw]⟩⟩
  exact ⟨ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.mpr hb.1)
    (LinearMap.range_eq_top.mpr hb.2), by ext; rfl⟩

private lemma phi_germ (hg : Good x) (φ : P × ℝ → ℝ) (hr : Reports (roll n) (window n x, 0) 0 φ) :
    ∀ᶠ v in 𝓝 (window n x), ∀ z : Series ℝ, window n z = v → Good z →
      Through n (record (fun t ↦ φ (v,t))) (reversion z) := by
  have H : roll n ((window n x,0),0) = 0 := by simp [roll, trunc, curve_zero, hg.1]
  have hV : Tendsto (fun v : P ↦ (v, (0:ℝ))) (𝓝 (window n x)) (𝓝 (window n x, (0:ℝ))) :=
    continuousAt_id.prodMk continuousAt_const
  filter_upwards [((hV.prodMk_nhds (show Tendsto (fun _ : P ↦ (0:ℝ)) _ _ from (tendsto_const_nhds (x := (0:ℝ))))).eventually hr.strict),
    hV.eventually (hr.diff.eventually (by simp)), hV.eventually (eventually_eventually_nhds.mpr hr.curves)] with v hv hvd hvh
  intro z hz₀ hz
  subst v
  have hbase : roll n ((window n z, (0:ℝ)),0) = 0 := by simp [roll, trunc, curve_zero, hz.1]
  let F (t : ℝ) := φ (window n z,t)
  have hφ : F 0 = 0 := hv.mp (hbase.trans H.symm)
  have hvp : Tendsto (fun i : ℝ ↦ (window n z, i)) (𝓝 (0:ℝ)) (𝓝 (window n z,0)) :=
    continuousAt_const.prodMk continuousAt_id
  have he : trunc z n ∘ F =ᶠ[𝓝 (0:ℝ)] id := by
    filter_upwards [hvp.eventually hvh] with w hw
    apply sub_eq_zero.mp
    change trunc z n (φ (window n z,w)) - w = (0:ℝ)
    simpa only [roll, poly_all] using hw.trans H
  have ht : ContDiffAt ℝ ω F 0 := hvd.comp (f := fun i : ℝ ↦ (window n z,i)) _
    (contDiffAt_const.prodMk contDiffAt_id)
  have hb := (record_zero_degree F).trans hφ
  have hd := ((trunc_represents z n).subJet (record_represents ht) hb).germ he.symm
  exact ((hz.reversion_inverts n).unique hb (hd.unique (record_represents contDiffAt_id))).symm

theorem tends_rev (hn : 1 ≤ n) (hg : Good x) (h : ∀ᶠ i in l, Good (X i))
    (hc : Converges n l X x) : Converges n l (fun i ↦ reversion (X i)) (reversion x) := by
  obtain ⟨φ, hφ⟩ := roll_solve hn hg
  have he := hc.tend_window
  have hh := phi_germ hg φ hφ
  have hd := mem_of_mem_nhds hh x rfl hg
  intro i hi
  have H : ContDiffAt ℝ ω (uncurry (fun (u : P) (t : ℝ) ↦ φ (u,t))) _ := hφ.diff
  have hr := (record_cont H i).tendsto.comp he
  rw [← hd i hi]
  apply hr.congr'
  filter_upwards [he.eventually hh, h] with w hw hw'
  exact hw (X w) rfl hw' i hi

end Invert
end YM.SchemeConversionRG11.Series
