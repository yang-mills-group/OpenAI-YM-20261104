import YM.Integration.WilsonCapturedPrimaryReading
import YM.Planned.ATOM_REGULAR_ESTIMATE.LogChart
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Smoothness at flat of the full captured density on each original finite
torus. The shrinking chart used here only establishes a germ. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimarySmooth
open Function Filter Set Metric Labels Wilson Lattice RG Source Push.Local
open ProjectorNext.Equivariance Next.Foundations Planned.AtomRegular
open WilsonCapturedPrimaryReading
open scoped Classical Topology ContDiff

theorem local_series {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (op : IsOpen s) (conn : IsPreconnected s) (k : ℕ) :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      (f : ℕ → E → V) (e : ℕ → ℝ), Summable e →
      (∀ i x, x ∈ s → ContDiffAt ℝ k (f i) x) →
      (∀ j ≤ k, ∀ i x, x ∈ s → ‖iteratedFDeriv ℝ j (f i) x‖ ≤ e i) →
      ContDiffOn ℝ k (fun x => ∑' i, f i x) s ∧
        ∀ x∈s, ‖iteratedFDeriv ℝ k (fun u => ∑' i, f i u) x‖ ≤ ∑' i, e i := by
  induction k with
  | zero =>
    intro V _ _ _ f e he hf hb
    have val i x (hx : x∈s) : ‖f i x‖ ≤ e i := by
      simpa only [norm_iteratedFDeriv_zero] using hb 0 le_rfl i x hx
    refine ⟨contDiffOn_zero.mpr (continuousOn_tsum
      (fun i x hx => (hf i x hx).continuousAt.continuousWithinAt) he val),?_⟩
    intro x hx
    rw [norm_iteratedFDeriv_zero]
    have sn := he.of_nonneg_of_le (fun i => norm_nonneg (f i x)) (fun i => val i x hx)
    exact (norm_tsum_le_tsum_norm sn).trans (sn.tsum_le_tsum (fun i => val i x hx) he)
  | succ k IH =>
    intro V _ _ _ f e he hf hb
    have diff i x (hx : x∈s) := (hf i x hx).differentiableAt (by simp)
    have hd x (hx : x∈s) : HasFDerivAt (fun u => ∑' i, f i u)
        (∑' i, fderiv ℝ (f i) x) x := by
      apply hasFDerivAt_tsum_of_isPreconnected he op conn
        (fun i y hy => (diff i y hy).hasFDerivAt) _ hx _ hx
      · intro i y hy
        simpa only [norm_iteratedFDeriv_one] using hb 1 (by omega) i y hy
      · exact Summable.of_norm_bounded he (fun i => by
          simpa only [norm_iteratedFDeriv_zero] using hb 0 (by omega) i x hx)
    have smooth' i x (hx : x∈s) : ContDiffAt ℝ k (fderiv ℝ (f i)) x := by
      have hall : ContDiffOn ℝ (k+1) (f i) s := fun y hy => (hf i y hy).contDiffWithinAt
      exact ((contDiffOn_succ_iff_fderiv_of_isOpen op).1 hall).2.2.contDiffAt (op.mem_nhds hx)
    have bounds' j (hj : j≤k) i x (hx : x∈s) :
        ‖iteratedFDeriv ℝ j (fderiv ℝ (f i)) x‖ ≤ e i := by
      rw [norm_iteratedFDeriv_fderiv]; exact hb _ (by omega) i x hx
    obtain ⟨smoothSum,boundSum⟩ := IH (fun i => fderiv ℝ (f i)) e he smooth' bounds'
    refine ⟨?_,?_⟩
    · rw [Nat.cast_add,Nat.cast_one]
      apply (contDiffOn_succ_iff_fderiv_of_isOpen op).2
      exact ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt,by simp,
        smoothSum.congr (fun x hx => (hd x hx).fderiv)⟩
    · intro x hx
      have same : fderiv ℝ (fun u => ∑' i, f i u) =ᶠ[𝓝 x] fun u => ∑' i, fderiv ℝ (f i) u := by
        filter_upwards [op.mem_nhds hx] with u hu; exact (hd u hu).fderiv
      rw [←norm_iteratedFDeriv_fderiv,(same.iteratedFDeriv (𝕜:=ℝ) k).eq_of_nhds]
      exact boundSum x hx

private theorem small_budget {n : Side} (P : BudgetPoint) (o : Site n) :
    ∃ T : BudgetPoint, T.threshold ≤ P.threshold ∧ T.order = P.order ∧
    T.power = P.power ∧ ∀ i : Link n, weight T o i ≤ 1 := by
  let S (i : Link n) : ℝ := (1+(separation i.1 o:ℝ))^P.power
  let M := 1 + ∑ i, S i
  have hS i : 0 ≤ S i := by unfold S; positivity
  have hM : 1 ≤ M := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hS i)
  have hMpos := zero_lt_one.trans_le hM
  have small : P.threshold/M ≤ P.threshold := div_le_self P.threshold_pos.le hM
  let T : BudgetPoint :=
    {P with
      threshold := P.threshold/M
      threshold_pos := div_pos P.threshold_pos hMpos
      threshold_le := small.trans P.threshold_le}
  refine ⟨T,small,rfl,rfl,fun i => ?_⟩
  change P.threshold/M * S i ≤ 1
  rw [div_mul_eq_mul_div,div_le_one hMpos]
  have hi : S i ≤ ∑ j, S j := Finset.single_le_sum (fun j _ => hS j) (Finset.mem_univ i)
  exact (mul_le_of_le_one_left (hS i) P.threshold_le).trans
    (hi.trans (le_add_of_nonneg_left zero_le_one))

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d} {A : Hol G}
variable {R : Rep G n} {B : SectionData F} {o : Site n}

private theorem regular_sum (order : d ≤ R.p.order) {q : Coefficient F n}
    (format : q.Format o A R) {κ price : ℝ} (paid : q.remBound o R κ price) :
    HasOrderAt (fun U => ∑' i, q.regular i U) 1 d := by
  obtain ⟨T,hT,ord,pow,small⟩ := small_budget R.p o
  obtain ⟨_,_,_,_,_,_,⟨e,mass,fee⟩,_⟩ := paid
  have esum : Summable e := mass.2.1.of_nonneg_of_le (fun i => (fee i).1)
    (fun i => R.p.loMass _ _ (fee i).1)
  have promote (X : Support n) (U : Config G n) (hU : Healthy T.threshold X U) :
      Healthy R.p.threshold X U := by
    apply hU.mono_right
    intro x hx
    obtain ⟨p,hx,hp⟩ := (flags_spec _ _ x).1 hx
    exact (flags_spec _ _ x).2 ⟨p,hx,hT.trans_lt hp⟩
  have reg (i : ℕ) : T.Regular (q.support i) (q.regular i) := by
    have h := format.smooth i
    refine ⟨h.sites,h.borel,h.symmetry,fun U hu => ?_, fun U hu b l hl => ?_⟩
    · rw [ord]; exact h.smooth U (promote _ _ hu)
    · exact h.hasDerivs U (promote _ _ hu) b l (ord ▸ hl)
  have bound (i : ℕ) : T.supBounds o (q.support i) (q.regular i) (e i) := by
    refine ⟨(fee i).1,fun U hu l hl dirs => (fee i).2 U (promote _ _ hu) l (ord ▸ hl) ?_⟩
    intro b hbl z
    exact (dirs b hbl z).trans (by rw [pow]; gcongr)
  let L := amp T o (G:=G)
  let W := bone T o (Finset.univ : Finset (Link n)) (G:=G)
  have W_eq (u : Directions G n) : W u = increment 1 (L u) := by
    unfold W bone; congr 1; funext i; simp [L,amp_apply,limitAmp]
  have W0 : W 0 = 1 := by rw [W_eq,map_zero,Work.G07.at_zero_increment]
  have cW : Continuous W := by
    rw [funext W_eq]
    exact (show Continuous (increment (1:Config G n)) by unfold increment; fun_prop).comp L.continuous
  have cut : ∀ᶠ u : Directions G n in 𝓝 0,
      flags T.threshold (W u) = ∅ ∧ ‖L u‖ ≤ 1 := by
    apply Filter.Eventually.and
    · exact ((W0 ▸ (cW.tendsto 0) :
        Tendsto W (𝓝 0) (𝓝 1)).eventually (offFlags T.threshold T.threshold_pos))
    · exact (L.continuous.norm.tendsto 0).eventually (ge_mem_nhds (by simp))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp cut
  let S : Set (Directions G n) := Metric.ball 0 r
  have hs (i : ℕ) (u : Directions G n) (hu : u∈S) :
      ContDiffAt ℝ d (q.regular i ∘ W) u ∧
      ∀ j ≤ d, ‖iteratedFDeriv ℝ j (q.regular i ∘ W) u‖ ≤ baseCost G d * e i := by
    obtain ⟨flags_zero,norm_le⟩ := hball hu
    apply base_bound (reg i) (bound i) (ord ▸ order)
    · unfold Healthy; rw [flags_zero]; simp
    · intro z _
      simpa [limitAmp,L] using (norm_le.trans' (norm_le_pi_norm (L u) z))
    · exact fun i _ => small i
  have sumSmooth := local_series (s:=S) Metric.isOpen_ball (convex_ball 0 r).isPreconnected d
    (fun i => q.regular i ∘ W) (fun i => baseCost G d*e i) (esum.mul_left _)
    (fun i u hu => (hs i u hu).1) (fun j hj i u hu => (hs i u hu).2 j hj)
  have totalChart := sumSmooth.1.contDiffAt (Metric.ball_mem_nhds _ hr)
  rw [← (suppress T o (G:=G)).map_zero] at totalChart
  have H := totalChart.comp (f:=suppress T o) 0
    ((suppress T o (G:=G)).contDiff.contDiffAt (x:=0) (n:=d))
  simpa [HasOrderAt,Function.comp_def,W_eq,L] using H

theorem original (hb : B.Sound A) (order : d ≤ R.p.order)
    (section_smooth : ∀ v, HasOrderAt (B.places v o) 1 d) {q : Coefficient F n}
    (format : q.Format o A R) {κ price : ℝ} (paid : q.remBound o R κ price) :
    HasOrderAt (reading B R o q) 1 d := by
  have total := regular_sum order format paid
  unfold HasOrderAt
  apply ContDiffAt.congr_of_eventuallyEq ((section_smooth (F.scaled R.p.threshold⁻¹ q.x)).add total)
  have tends : Tendsto (increment (1:Config G n)) (𝓝 0) (𝓝 1) := by
    simpa only [Work.G07.at_zero_increment] using
      (show Continuous (increment (1:Config G n)) by unfold increment; fun_prop).tendsto 0
  filter_upwards [tends.eventually (offFlags R.p.threshold R.p.threshold_pos)] with u hu
  exact on_clear hb q hu

end YM.Integration.WilsonCapturedPrimarySmooth
