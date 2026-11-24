import YM.Comparison.Density.Mirrors.Ledger

/-!
Per-centre analytics in the vacuum conversion. `given` is the actual
signed list of old terms (includes prefactors). Their W is evaluated
using **actual** masks and limited to the total region specified. We
only use `paid` (circle unused here) in these masks, not unaggregated
smallness comparable to the final error. They needn't use the output
mask. `mode` only tests their sum on the stronger common mask. Path,
address and any earlier queries must be in Y (except for UsesFinal,
whose inspected links must be counted when pushing at input).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Convert
open Mirrors Transport RG Lattice Wilson
open Function MeasureTheory Finset AnalyticBridge.SectorAffine.Offset
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge} (B : BudgetPoint) (L : LinkTube G)

structure Short (G : Gauge) (n : Side) where
  r : Side
  k : Side
  D : ℕ
  -- real analytic radius covers the axial bill. e is tiny held-jet
  -- price; d is only a moderate analytic hull-test price.
  w : ℝ
  d : ℝ
  e : ℝ
  m : ℕ
  s : ℕ
  f : Links ℤ G.El → ℝ
  prefactor : ℝ
  Y : ℕ→ Site n → Support n
  given : ℕ → Site n → Config G n→ℝ
  price : ℕ→ℝ
  old : ℝ
  -- absolute price BEFORE comparing to desired formal answer
namespace Short
variable (T : Short G n)

-- payload carries mask decisions explicitly in the function given
-- (whether termwise masked, direct clipped, predicate, or scalar) and
-- is a SUM of signed entries subtracted from the exponent.
def comes (o : Site n) (U : Config G n) := ∑' i, T.given i o U

structure Staged (B : BudgetPoint) (L : LinkTube G) (T : Short G n) : Prop where
  radius : T.r.val < T.k.val
  advance : T.k.val+4 < T.D
  horiz : Room B n L T.D T.w
  injectR : 4*T.r.val<n.val
  snap : 2*(T.r.val+3)< n.val
  field : B.order ≤ T.m
  order : T.s≤ T.m
  nneg : 0≤T.d ∧ 0≤T.e
  covers : LocalOn (Lattice.box T.r.val) T.f
  groups : GaugeInvariant T.f
  borel : Measurable T.f
  signed U s : T.f (pull s 0 U)= T.f U
  upper A : ‖A‖≤ T.w → Through T.m (chart T.r T.f) A T.d
  lower : Ordinary T.f n T.s T.e
  stubs i x : T.Y i x ⊆ neighborhood T.r.val x
  observes i x : GaugeInvariant (T.given i x)
  reads i x : UsesFinal B.threshold (T.Y i x) (T.given i x)
  meas i x : Measurable (T.given i x)
  amount : SumBudget T.price T.old
  paid i x U : |T.given i x U| ≤ T.price i
  oriented x b s U : T.comes x (pull s b U)=T.comes (affine s b x) U
  mode x U : Healthy B.threshold (neighborhood T.r.val x) U → T.comes x U=T.prefactor*T.f (expandAt x U)

def proceeds (o : Site n) := T.prefactor • Mirrors.restored T.f T.k o

def loadData : ℝ := |T.prefactor| * packetBudget B L T.k T.s T.w T.d T.e

variable {B T L} (h : Staged B L T)
include h

lemma measured (o : Site n) : B.Regular (neighborhood T.D o) (T.proceeds o) ∧ B.supBounds o (neighborhood T.D o) (T.proceeds o) (T.loadData B L) := by
  obtain ⟨H,hS⟩:=transport_mirror B L T.f T.r T.k o T.D h.horiz h.advance h.field h.order h.radius
    h.injectR h.nneg.1 h.nneg.2 h.borel h.covers h.groups h.lower h.upper
  exact ⟨AnalyticBridge.CouplingShape.reg_scale _ H,AnalyticBridge.CouplingShape.sup_scale _ hS⟩

lemma proceeds_s (o x : Site n) (s) (U) : T.proceeds (affine s x o) U=T.proceeds o (pull s x U) := by
  simp only [proceeds, Pi.smul_apply, Mirrors.restored_signed _ _ _ _ _ h.signed U]

private lemma comes_gauge (o) : GaugeInvariant (T.comes o) := fun k U=> tsum_congr fun i=> h.observes i o k U
private lemma comes_price (o U) : ‖T.comes o U‖ ≤ T.old:= by
  have he := h.amount.2.1.of_nonneg_of_le (fun i=> norm_nonneg (T.given i o U)) fun i=> h.paid i _ _
  exact (norm_tsum_le_tsum_norm he).trans ((he.tsum_le_tsum (fun i=> h.paid i o U) h.amount.2.1).trans h.amount.2.2)

omit h
variable (T B)

def S := T.prefactor • T.f
def projCost (o : Site n) := maskCost B T.S T.r.val o
def remask (o : Site n) := flagLog B T.S T.r.val T.k T.D o
def waste (o : Site n) := T.projCost B o-T.comes o-T.remask B o

def gained (o : Site n) (U) := masked B.threshold (neighborhood T.D o) (T.proceeds o) U

-- Whole flag price. Includes moving original and rendered terms
-- on all masks. Any later exponent amplification is still separate.
def loss := 2*T.old + issue T.k T.old

lemma balance (U : Config G n) : ∑ x, T.waste B x U-∑ x, T.gained B x U= -∑ x,T.comes x U := by
  have hz x : T.gained B x U= maskGain B T.S T.k T.D x U:= by
    unfold gained maskGain; congr! 2; funext y V; rw [proceeds,Pi.smul_apply,smul_eq_mul,restored_value, restored_value,mul_sum]
    refine sum_congr rfl fun j _=>?_
    rw [mul_left_comm,mul_sum]; apply congr_arg
    exact sum_congr rfl fun _ _=> rfl
  have hp:= accounted B T.S T.r.val T.k T.D U
  simp only [waste,Pi.sub_apply,sum_sub_distrib,hz,projCost,remask,hp]; ring

variable {T B}
include h
private lemma S_gauge : GaugeInvariant T.S := by intro v U; simp only [S,Pi.smul_apply,h.groups v]
private lemma S_orients U s : T.S (pull s 0 U) = T.S U := by simp [S, h.signed]
private lemma S_reads : LocalOn (Lattice.box T.r.val) T.S := by intro U V ht; simp only [S, Pi.smul_apply,h.covers U V ht]
private lemma S_meas : Measurable T.S := measurable_const.smul h.borel
lemma fits (x : Site n) : UsesFinal B.threshold (neighborhood (2*T.D) x) (T.waste B x):= by
  have he: T.r.val ≤ 2*T.D:= by have hh:=h.advance; have ht:=h.radius; omega
  intro U V hA hg
  simp only [waste,Pi.sub_apply]; refine congrArg₂ (·-·) (congrArg₂ (·-·) ?_ ?_) ?_
  · exact Work.H03.reads_larger (neighborhood_mono he) (masked_reads B (local_expand _ _ x (S_reads h))) U V hA hg
  · exact tsum_congr fun i=> Work.H03.reads_larger ((h.stubs i x).trans (neighborhood_mono he)) (h.reads i x) U V hA hg
  exact flag_reads B _ _ _ _ (S_reads h) h.radius.le h.advance.le x U V hA hg
lemma waste_gauge (o) : GaugeInvariant (T.waste B o):= by
  intro z U; exact congrArg₂ (·-·) (congrArg₂ (·-·) (masked_gauge _ _ _ (entry_gauge _ (S_gauge h) o) z U) (comes_gauge h o z U)) (flag_gauge _ _ _ _ _ (S_gauge h) _ z U)
lemma waste_orients b s x U : T.waste B (affine s b x) U=T.waste B x (pull s b U) := by
  refine congrArg₂ (·-·) (congrArg₂ (·-·) ?_ (h.oriented x b s U).symm) (flag_moves _ _ _ _ _ x b s (S_orients h) U)
  unfold projCost maskCost; rw [neighborhood_signed]; exact masked_signed _ _ _ _ (by rw [comp_apply,comp_apply,expandAt_pull,S_orients h])
lemma waste_meas (x) : Measurable (T.waste B x) := by
  apply Measurable.sub _ (flag_borel _ _ _ _ _ (S_meas h) _)
  apply Measurable.sub _ (Measurable.tsum fun i=> h.meas i x)
  exact masked_measurable _ _ _ ((S_meas h).comp (show Continuous (expandAt x (K:=G.El)) from by unfold expandAt; fun_prop).measurable)
lemma matchedCost (x U) (he : Healthy B.threshold (neighborhood T.r.val x) U) : T.projCost B x U= T.comes x U := by
  simp only [projCost,maskCost,masked_eq _ _ _ _ he,h.mode x U he]; rfl
lemma wasted_bad (x U) (he : Healthy B.threshold (neighborhood (2*T.D) x) U) : T.waste B x U=0 := by
  have hp : T.r.val≤2*T.D:= by have hh:=h.advance; have ht:=h.radius; omega
  simp only [waste, Pi.sub_apply, matchedCost h x U (Finset.disjoint_of_subset_left (neighborhood_mono hp) he), sub_self, remask, cost_agreement _ _ _ _ h.radius.le _ _ h.advance.le _ (S_orients h) (S_reads h) he]
lemma charge (o U) : ‖T.waste B o U‖ ≤ T.loss := by
  have he : 0 ≤ T.old := Push.AbsoluteSums.budget_nonneg h.amount
  have hf x V : ‖T.projCost B x V‖ ≤ T.old:= by
    by_cases hz: Healthy B.threshold (neighborhood T.r.val x) V
    · rw [matchedCost h x V hz]; exact comes_price h x V
    rw [projCost,maskCost,masked_ne _ _ _ _ hz,norm_zero]; exact he
  simp only [loss, two_mul]; exact (norm_sub_le ..).trans (add_le_add ((norm_sub_le ..).trans (add_le_add (hf o U) (comes_price h o U))) (flag_sup B _ T.r T.k h.snap _ h.advance.le _ he (S_reads h) hf o U))
end Short
end YM.Comparison.Density.Convert
