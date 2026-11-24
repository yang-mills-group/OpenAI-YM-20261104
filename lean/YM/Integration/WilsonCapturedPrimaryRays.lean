import YM.Integration.WilsonCapturedPrimaryCollar

/-! The local physical probe is the exponential of the finite Taylor polynomial
of the original Hol.testLinks logarithm. Its measured jet is exactly the
original one on all retained supports, including at positive degree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryRays
open Function Filter Finset Set Labels Lattice Wilson RG Source Push.Local
open Next.Foundations ProjectorNext.Equivariance Trace.Physical.Germ
open WilsonCapturedPrimaryReading WilsonCapturedPrimaryCollar
open scoped Classical Topology ContDiff

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def polynomial (D : ℕ) (u : ℝ → E) (t : ℝ) : E := ∑ i∈range (D+1),
  t^i • ((i.factorial:ℝ)⁻¹ • iteratedDeriv i u 0)

theorem polynomial_smooth (D : ℕ) (u : ℝ → E) : ContDiff ℝ ∞ (polynomial D u) := by
  unfold polynomial; fun_prop

theorem polynomial_jet (u : ℝ → E) {k D : ℕ} (h : k ≤ D) :
    iteratedDeriv k (polynomial D u) 0 = iteratedDeriv k u 0 := by
  have smooth (i : ℕ) : ContDiffAt ℝ k (fun t : ℝ => t^i) 0 := by fun_prop
  unfold polynomial
  rw [iteratedDeriv_fun_sum (I:=range (D+1))
    (f:=fun i (t:ℝ) => t^i • ((i.factorial:ℝ)⁻¹ • iteratedDeriv i u 0))
    (fun i _ => by fun_prop)]
  simp only [iteratedDeriv_smul_const (smooth _),iteratedDeriv_fun_pow_zero]
  rw [sum_eq_single_of_mem k (mem_range.mpr (Nat.lt_succ_of_le h))]
  · simp [smul_smul,Nat.factorial_ne_zero]
  · intro i _ hi; simp [Ne.symm hi]

theorem homogeneous (P : ℝ → E) {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (f : E → A) (D k : ℕ) (hk : k ≤ D) (hf : ContDiffAt ℝ D f (P 0))
    (hP : ContDiffAt ℝ D P 0) :
    iteratedDeriv k (f ∘ P) 0 = iteratedDeriv k (f ∘ polynomial D P) 0 := by
  have flat : polynomial D P 0 = P 0 := by simpa only [iteratedDeriv_zero] using
    (polynomial_jet P (Nat.zero_le D))
  have hp : ContDiffAt ℝ D (polynomial D P) 0 := (polynomial_smooth D P).contDiffAt.of_le (by exact_mod_cast le_top)
  rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition hf hP (Nat.cast_le.mpr hk),
    iteratedDeriv_vcomp_eq_sum_orderedFinpartition (flat.symm ▸ hf) hp (Nat.cast_le.mpr hk),flat]
  apply sum_congr rfl
  intro c _
  congr 1
  funext i
  exact (polynomial_jet P ((c.partSize_le i).trans hk)).symm

theorem clip_continuous (o : Site n) (r : ℕ) :
    Continuous (clip (G:=G) o r) := continuous_pi fun e => by
  by_cases h : separation e.1 o ≤ r
  · simp only [clip,if_pos h]; exact continuous_apply e
  · simp only [clip,if_neg h]; exact continuous_const

variable {A : Hol G} {B : SectionData F} {o : Site n} {R : Rep G n}

/-- The same retained signed coefficient reads any two healthy fields agreeing
on the entire enrolled collar. -/
theorem locality (hb : B.Sound A) {q : Coefficient F n} (form : q.Format o A R)
    (K : ℕ) (stencil : ∀ x∈B.footprint o, separation x o ≤ radius R.p K)
    (U : Config G n) (hU : flags R.p.threshold U = ∅)
    (hW : flags R.p.threshold (clip o (radius R.p K) U) = ∅) :
    reading B R o (kept q R.p K) U = reading B R o (kept q R.p K) (clip o (radius R.p K) U) := by
  rw [on_clear hb _ hU,on_clear hb _ hW]
  congr 1
  · exact B.placed_local o _ _ _ (fun l h _ => (if_pos (stencil l.1 h)).symm)
  · apply tsum_congr
    intro i
    by_cases h : coverNumber R.p.B (q.support i) < K
    · simpa only [kept,if_pos h] using (retained form h U).symm
    · simp [kept,h]

def field (A : Hol G) (P : BudgetPoint) (o : Site n) (r : ℕ) (p : Probe G d) (t : ℝ) : Config G n :=
  clip o r (increment 1 (polynomial d (testLog A d o (P.threshold • p.1)) t))

theorem probe (hb : B.Sound A) {q : Coefficient F n} (form : q.Format o A R)
    {κ s : ℝ} (paid : q.remBound o R κ s) (order : d ≤ R.p.order) (power : d ≤ R.p.power)
    (size : ∀ x ∈ B.stencil, ∀ i : Axis, 20*((x i).natAbs+1) ≤ n.val)
    (section_smooth : ∀ v, HasOrderAt (B.places v o) 1 d)
    (K : ℕ) (stencil : ∀ x∈B.footprint o, separation x o ≤ radius R.p K) (p : Probe G d) :
    runProbe F p (projection F A R.p.threshold o (kept q R.p K)) =
      iteratedDeriv p.2.val (reading B R o (kept q R.p K) ∘ field A R.p o (radius R.p K) p) 0 := by
  obtain ⟨kf,kp⟩ := funded form paid K
  let f := reading B R o (kept q R.p K)
  let u := testLog A d o (R.p.threshold • p.1)
  have su := (testLog_diff A d o (R.p.threshold • p.1)).of_le (by exact le_top : (d:WithTop ℕ∞)≤ω)
  have sf := WilsonCapturedPrimarySmooth.original hb order section_smooth kf kp
  rw [WilsonCapturedPrimaryReading.probe hb size order power section_smooth kf kp sf p]
  let U := increment (1:Config G n) ∘ polynomial d u
  have ray0 : polynomial d u 0 = 0 := by
    simpa only [iteratedDeriv_zero,testLog_zero,u] using polynomial_jet u (Nat.zero_le d)
  have cont : Continuous U := (by unfold increment; fun_prop : Continuous (increment (1:Config G n))).comp
    (polynomial_smooth d u).continuous
  have u0 : U 0 = 1 := by simp only [U,comp_apply,ray0,Work.G07.at_zero_increment]
  have w0 : clip o (radius R.p K) (U 0) = 1 := by
    rw [u0]; funext e; simp [clip]
  have Uw : Tendsto U (𝓝 0) (𝓝 1) := u0 ▸ cont.tendsto 0
  have Ww : Tendsto (clip o (radius R.p K) ∘ U) (𝓝 0) (𝓝 1) :=
    w0 ▸ ((clip_continuous o _).comp cont).tendsto 0
  have near : (f ∘ U) =ᶠ[𝓝 0] f ∘ field A R.p o (radius R.p K) p := by
    filter_upwards [Uw.eventually (offFlags _ R.p.threshold_pos),
      Ww.eventually (offFlags _ R.p.threshold_pos)] with t h1 h2
    exact locality hb form K stencil (U t) h1 h2
  have smooth : ContDiffAt ℝ d (f ∘ increment 1) (u 0) := by
    change ContDiffAt ℝ d (f ∘ increment 1) (testLog A d o (R.p.threshold • p.1) 0)
    rw [testLog_zero]; exact sf
  exact (((increment_testLog A d o (R.p.threshold • p.1)).fun_comp f).iteratedDeriv_eq p.2.val).trans
    ((homogeneous u _ d _ (Nat.le_of_lt_succ p.2.isLt) smooth su).trans (near.iteratedDeriv_eq p.2.val))

end YM.Integration.WilsonCapturedPrimaryRays
