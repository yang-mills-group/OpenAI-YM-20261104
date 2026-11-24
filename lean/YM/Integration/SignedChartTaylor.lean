import YM.Integration.ActualWilsonPacketGerms
import YM.Integration.WilsonChartSmoothSeries
import Mathlib.Analysis.Calculus.Taylor

/-! Field Taylor bounds for every mixed marked component of the purchased physical Wilson source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedChartTaylor
open Lattice Wilson RG Marker Exterior Function Finset Set Metric
open Comparison.Density.RenderM LocalComparison
open AnalyticBridge.SectorAffine.Offset Push.AbsoluteSums ActualWilsonPacketGerms
open scoped Classical BigOperators Topology ContDiff
variable {G : Gauge} {V : Type} [DecidableEq V] {n : Side}
    {D : V → ComparisonDensity.Address.Orbit} {R : Census V} {P : MarkedPackets D G n R}
    {w : V → ℝ} {g width budget : ℝ} {β : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n} {off slope : ℕ}
    (H : P.Paid β address region w g width budget off slope)

/-- The weighted scalar component of an actual source, with its independently selectable packet rows. -/
def component (P : MarkedPackets D G n R) (w : V → ℝ) (g : ℝ) (s : R.Mode) (keep : ℕ → Prop)
    (x : IndependentTests D) (A : Directions G n) : ℂ :=
  ∑' i,if P.mode i=s ∧ keep i then Poly.toll w s • P.term (testInclusion D x) g (increment 1 A) i else 0

section Recorded
variable [Fintype V]

/-- Select one marked component with exactly the original product of its independent radii. -/
def take (w : V → ℝ) (s : R.Mode) : Poly R →L[ℝ] ℂ := Poly.toll w s • ContinuousLinearMap.proj s

omit [Fintype V] in
theorem recorded (P : MarkedPackets D G n R) (w : V → ℝ) (s : R.Mode) (keep : ℕ → Prop)
    (x : IndependentTests D) (g : ℝ) (A : Directions G n)
    (hs : Summable (fun i => Poly.send (P.mode i) (P.term (testInclusion D x) g (increment 1 A) i))) :
    component P w g s keep x A=take w s (∑' i,if keep i then Poly.send (P.mode i)
      (P.term (testInclusion D x) g (increment 1 A) i) else 0) := by
  let b (i : ℕ) : Poly R := if keep i then Poly.send (P.mode i) (P.term (testInclusion D x) g (increment 1 A) i) else 0
  have hb : Summable b := by
    refine (hs.indicator {i | keep i}).congr fun i => ?_
    by_cases h : keep i <;> simp [b,h]
  change _=take w s (∑' i,b i)
  rw [←((take w s).hasSum hb.hasSum).tsum_eq]
  apply tsum_congr
  intro i
  change (if P.mode i=s ∧ keep i then _ else _)=Poly.toll w s • (b i).part s
  by_cases h : keep i
  · have kept : b i=Poly.send (P.mode i) (P.term (testInclusion D x) g (increment 1 A) i):=if_pos h
    by_cases e : P.mode i=s
    · rw [if_pos (And.intro e h),kept,Poly.part_send,if_pos e.symm]
    · rw [if_neg (fun he=>e he.1),kept,Poly.part_send,if_neg (Ne.symm e),smul_zero]
  · rw [if_neg (fun he=>h he.2),show b i=0 from if_neg h,Poly.part_nil,smul_zero]

end Recorded

private def charge (P : MarkedPackets D G n R) (w : V → ℝ) (g width : ℝ) (v : V) (i : ℕ) : ℝ :=
  if v∈(P.mode i).val then match P.packet i with
    | none => 0
    | some T => Poly.toll w (P.mode i)*‖(g:ℂ)^P.power i‖*T.coin*Real.exp (width*T.fall)
  else 0

private theorem zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (A : E) {c : ℝ} (hc : 0≤c) : Through k (fun _ : E => (0:ℂ)) A c :=
  ⟨contDiffAt_const,fun j _ => by simpa only [iteratedFDeriv_fun_zero,Pi.zero_apply,norm_zero] using hc⟩

include H in
/-- The derivatives of a complete mixed component sum inside the unit chart. Every emitted mode is charged to any one member of its original marked set. -/
theorem at_field (s : R.Mode) (v : V) (hv : v∈s.val) (keep : ℕ → Prop) (x : IndependentTests D)
    (k cap : ℕ) (hcap : P.rankCap≤cap) (A : Directions G n) (hA : ‖A‖<1) :
    Through k (component P w g s keep x) A (amplifier G cap k width*budget) := by
  let f (i : ℕ) (B : Directions G n) : ℂ := if P.mode i=s ∧ keep i then
    Poly.toll w s • P.term (testInclusion D x) g (increment 1 B) i else 0
  let c := charge P w g width v
  let K := amplifier G cap k width
  have hc : SumBudget c budget := by
    refine (congrArg (fun f : ℕ→ℝ=>SumBudget f budget) ?_).mpr (H.roots v)
    funext i
    by_cases seated : v∈(P.mode i).val
    · cases packet : P.packet i <;> simp [c,charge,seated,packet]
    · simp [c,charge,seated]
  have hK : 0≤K := amplifier_nonneg G cap k H.width_pos
  have hf (i : ℕ) (B : Directions G n) (hB : B∈ball 0 1) : Through k (f i) B (K*c i) := by
    have hB' : ‖B‖≤1 := le_of_lt (by simpa only [mem_ball,dist_zero_right] using hB)
    have hci : 0≤K*c i := mul_nonneg hK (hc.1 i)
    by_cases he : P.mode i=s ∧ keep i
    · have hvi : v∈(P.mode i).val := he.1.symm ▸ hv
      cases ht : P.packet i with
      | none => simpa [f,he,MarkedPackets.term,ht] using zero k B hci
      | some T =>
        have htoll := (Poly.worth H.positive s).le
        have h := (chart_term H ht x k B hB').scale (Poly.toll w s)
        rw [abs_of_nonneg htoll] at h
        have hl := visit H ht k cap hcap
        have hlast : Poly.toll w s*(‖(g:ℂ)^P.power i‖*Token.stamp k T)≤K*c i := by
          dsimp only [c,charge,K]
          rw [if_pos hvi,ht,he.1]
          calc
            _ ≤ Poly.toll w s*(‖(g:ℂ)^P.power i‖*(amplifier G cap k width*(T.coin*Real.exp (width*T.fall)))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl (norm_nonneg _)) htoll
            _ = _ := by ring
        simpa only [f,if_pos he,Function.comp_apply] using h.mono hlast
    · simpa only [f,if_neg he] using zero k B hci
  have hs := WilsonChartSmoothSeries.summed isOpen_ball (convex_ball ..) hf (hc.2.1.mul_left K) A
    (by simpa only [mem_ball,dist_zero_right] using hA)
  have hcost : (∑' i,K*c i) ≤ K*budget := by rw [tsum_mul_left];exact mul_le_mul_of_nonneg_left hc.2.2 hK
  exact hs.mono hcost

section Ray
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def jet (F : E → ℂ) (A : E) (j : ℕ) : ℂ :=
  (j.factorial:ℝ)⁻¹ • iteratedDeriv j (fun t : ℝ => F (t • A)) 0

private theorem derivative (F : E → ℂ) (A : E) (j : ℕ) (t : ℝ) (h : ContDiffAt ℝ j F (t • A)) :
    iteratedDeriv j (fun u : ℝ => F (u • A)) t=iteratedFDeriv ℝ j F (t • A) (fun _ => A) := by
  let D : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight A
  change (iteratedFDeriv ℝ j (F ∘ D) t) (fun _ => 1)=_
  rw [Push.Uniform.iter_lin_at (L:=D) h]
  simp [D,ContinuousMultilinearMap.compContinuousLinearMap_apply]

theorem window (F : E → ℂ) (A : E) (k : ℕ) (t c : ℝ) (ht : 0<t) (hr : t*‖A‖<1)
    (h : ∀ B : E,‖B‖<1 → Through (k+1) F B c) :
    ‖F (t • A) - ∑ j∈range (k+1), t^j • jet F A j‖ ≤ c*(t*‖A‖)^(k+1)/(k.factorial:ℝ) := by
  let f := fun u : ℝ => F (u • A)
  let D : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight A
  have hA (u : ℝ) (hu : u∈Icc 0 t) : ‖u • A‖<1 := by
    rw [norm_smul,Real.norm_of_nonneg hu.1]
    exact (mul_le_mul_of_nonneg_right hu.2 (norm_nonneg A)).trans_lt hr
  have hf (u : ℝ) (hu : u∈Icc 0 t) : ContDiffAt ℝ (k+1:ℕ) f u :=
    (h _ (hA u hu)).smooth.comp u D.contDiff.contDiffAt
  have hd (j : ℕ) (hj : j≤k+1) (u : ℝ) (hu : u∈Icc 0 t) :
      iteratedDerivWithin j f (Icc 0 t) u=iteratedDeriv j f u :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht)
      ((hf u hu).of_le (by exact_mod_cast hj)) hu
  have hbound (u : ℝ) (hu : u∈Icc 0 t) : ‖iteratedDerivWithin (k+1) f (Icc 0 t) u‖ ≤ c*‖A‖^(k+1) := by
    rw [hd _ le_rfl u hu,derivative F A _ u (h _ (hA u hu)).smooth]
    exact ((iteratedFDeriv ℝ (k+1) F (u • A)).le_opNorm (fun _ => A)).trans (by
      simpa only [prod_const,card_univ,Fintype.card_fin] using mul_le_mul_of_nonneg_right ((h _ (hA u hu)).pay _ le_rfl) (pow_nonneg (norm_nonneg A) (k+1)))
  have htay := taylor_mean_remainder_bound ht.le (fun u hu => (hf u hu).contDiffWithinAt)
    (right_mem_Icc.mpr ht.le) hbound
  have hpoly : taylorWithinEval f k (Icc 0 t) 0 t = ∑ j∈range (k+1),t^j • jet F A j := by
    rw [taylor_within_apply]
    apply sum_congr rfl
    intro j hj
    have hle : j≤k+1 := (mem_range.mp hj).le
    rw [hd j hle 0 (left_mem_Icc.mpr ht.le),sub_zero]
    simp only [jet,smul_smul,f]
    rw [mul_comm]
  rw [hpoly,sub_zero] at htay
  refine htay.trans_eq ?_
  rw [mul_pow]
  ring

end Ray

include H in
/-- At the original physical coupling, with any mixed family and any subset of true rows, field truncation has an explicit remainder throughout the native chart. -/
theorem purchased (s : R.Mode) (v : V) (hv : v∈s.val) (keep : ℕ → Prop) (x : IndependentTests D)
    (k cap : ℕ) (hcap : P.rankCap≤cap) (A : Directions G n) (t : ℝ) (ht : 0<t) (hr : t*‖A‖<1) :
    let F := component P w g s keep x
    ‖F (t • A)-∑ j∈range (k+1),t^j • jet F A j‖ ≤
      amplifier G cap (k+1) width*budget*(t*‖A‖)^(k+1)/(k.factorial:ℝ) :=
  window _ A k t _ ht hr (at_field H s v hv keep x (k+1) cap hcap)

end YM.Integration.SignedChartTaylor
