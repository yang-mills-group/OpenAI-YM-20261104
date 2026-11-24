import YM.Comparison.Density.Fusing.Alphabet
import YM.Comparison.Density.Mirrors.Anchor

/-!
Marker packets tested with any root held; path addresses are not
identified. Registers adds only NONEMPTY log coefficients. Static
coordinates carried by these kernels inside their real masks; if
source germs need a root-primary or global extraction, it operates
on the represented log and emits its own force adjustment.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Convert
open Fusing Mirrors Transport RG Lattice Wilson Markers Registers Testing MeasureTheory
open Function Finset Push.AbsoluteSums Marker Multi AnalyticBridge.SectorAffine.Offset
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side}
variable {V : Type} [DecidableEq V] {R : Census V} {X : V → Type} [∀ v, NormedAddCommGroup (X v)] [∀ v, NormedSpace ℂ (X v)]

structure Crown (G : Gauge) (X : V→Type) (n : Side) where
  center : Site n
  k : ℕ
  D : ℕ
  Y : Support n
  f : Cross X → Config G n→ℂ
  factor : ℂ
  pieces : ℕ→Support n
  W : ℕ→Cross X→ Config G n→ℂ
  m : ℕ
  s : ℕ
  w : ℝ
  d : ℝ
  e : ℝ
  costs : ℕ→ℝ
  tally : ℝ

variable (B : BudgetPoint) (K : LinkTube G) {O : Readers V X n} {i : Hot R}

namespace Crown
variable (T : Crown G X n)

def grows (x : Cross X) (U : Config G n) := ∑' j,T.W j x U
def backs (x : Cross X) := T.factor • T.f x
def plot := neighborhood T.D T.center
def drift (x : Cross X) := T.grows x - RG.masked B.threshold T.plot (T.backs x)
def tab := ‖T.factor‖ * (Anchor.focus T.k T.D B ^ B.order * (groupPrice K B.order * (T.s*T.e+T.d*T.w^T.s)))

structure Allocated (O : Readers V X n) (B : BudgetPoint) (K : LinkTube G) (i : Hot R) (T : Crown G X n) : Prop where
  radius : Room B n K T.D T.w
  fits : T.k<T.D
  pays v : v∈i.sites → O.source.uses v⊆ T.plot
  boundLinks : T.Y⊆ neighborhood T.k T.center
  intervals j : T.pieces j ⊆ T.plot
  rooted j v : v∈i.sites → O.source.uses v ⊆ T.pieces j
  givenGauge x : GaugeInvariant (T.f x)
  stencils x : LocalOn T.Y (T.f x)
  measurable x : Measurable (T.f x)
  graded U : Slotted i.sites (fun x=> T.f x U)
  reads U : Reads O.locus T.plot i.sites (fun x=> T.f x U)
  order : B.order ≤ T.m
  full : T.s ≤ T.m
  size : 0≤T.d ∧ 0≤T.e
  field x : UnitPage x → ∀ A : Directions G n, ‖A‖≤T.w → Through T.m (T.f x ∘ increment 1) A T.d
  jets x : UnitPage x → ∀ a < T.s, ‖iteratedFDeriv ℝ a (T.f x ∘ increment 1) 0‖≤ T.e
  sectors j x : GaugeInvariant (T.W j x)
  meas j x : Measurable (T.W j x)
  flags j x : UsesFinal B.threshold (T.pieces j) (T.W j x)
  spins j U : Slotted i.sites (fun x=> T.W j x U)
  tracks j U : Reads O.locus (T.pieces j) i.sites (fun x=> T.W j x U)
  fee : SumBudget T.costs T.tally
  costs x : UnitPage x → ∀ j U, ‖T.W j x U‖ ≤ T.costs j
  side x U : Healthy B.threshold T.plot U → T.grows x U = T.backs x U

variable {T B K} (h : Allocated O B K i T)
include h
lemma buys (x : Cross X) (he : UnitPage x) (v : V) (hv : v∈i.sites) :
    B.Regular T.plot (T.backs x) ∧ B.supBounds (O.source.root v) T.plot (T.backs x) (T.tab B K):=
  ⟨Next.Foundations.regular_smul _ (Anchor.aligned B K _ h.boundLinks h.fits h.radius h.order (h.measurable x) (h.stencils _) (h.givenGauge _) (h.field x he)),
    Next.Foundations.bound_smul _ (Anchor.pay B K _ _ ((neighborhood_iff ..).mp (h.pays v hv (O.source.listed v))) h.boundLinks h.fits h.radius h.order h.full h.size.1 h.size.2 (h.stencils _) (h.givenGauge _) (h.field x he) (h.jets x he))⟩
omit h
lemma zeroRegular (X : Support n) (o : Site n) : B.Regular X (fun _ : Config G n=> (0:ℂ)) ∧ B.supBounds o X (fun _ : Config G n=> (0:ℂ)) 0:= by
  simpa only [Finset.sum_empty] using! (Next.Foundations.regular_bound_sum (P:=B) (s:=X) (o:=o) (∅:Finset ℕ) (fun _ _ => (0:ℂ)) (fun _=>0) (G:=G) (fun i hi=> False.elim (notMem_empty i hi)))
include h
variable [Fintype V]

omit [Fintype V] in
lemma backs_occ (U) : Slotted i.sites (fun x=> T.backs x U) := (h.graded U).scale _
lemma purchased (x : Cross X) : B.Regular T.plot (T.backs x):= by
  obtain ⟨v,hv⟩:=i.property; obtain ⟨a,y,hy,rfl⟩:=Testing.normalize x
  rw [show T.backs (a • y)=_ from funext (fun U=> show T.backs (a • y) U=(a^i.sites.card • T.backs y) U from (backs_occ h U).stretch a y)]
  exact Next.Foundations.regular_smul _ (buys h y hy v hv).1
lemma income (x U) : Summable fun j=> T.W j x U:= by
  obtain ⟨p,y,hv,rfl⟩:= Testing.normalize x
  have he j : T.W j (p • y) U=p^i.sites.card • T.W j y U:= (h.spins j U).stretch p y
  simp_rw [he]; exact (h.fee.2.1.of_nonneg_of_le (fun j=> norm_nonneg _) (fun j=> h.costs y hv j U)).of_norm.const_smul _

lemma drift_tracks (U) : Slotted i.sites (fun x=> T.drift B x U) ∧ Reads O.locus T.plot i.sites (fun x=> T.drift B x U) := by
  by_cases ht: Healthy B.threshold T.plot U
  · simp_rw [drift,Pi.sub_apply,masked_eq _ _ _ _ ht,h.side _ _ ht,sub_self]; exact ⟨Slotted.vacant,fun _ _ _=>rfl⟩
  simp_rw [drift,Pi.sub_apply,masked_ne _ _ _ _ ht,sub_zero]; unfold grows
  refine ⟨Slotted.series _ (fun j=> h.spins j U) (fun x=> income h x U), fun x y hh=> tsum_congr fun j=>?_⟩
  exact h.tracks j U x y fun s hs=> O.locus.tighter s _ _ (h.intervals j) _ _ (hh s hs)

omit [Fintype V] in
lemma drift_support (x : Cross X) : UsesFinal B.threshold T.plot (T.drift B x) ∧ (∀ U, Healthy B.threshold T.plot U → T.drift B x U=0) := by
  unfold drift
  refine ⟨fun U V hp hv=> congrArg₂ Sub.sub ?_ ?_,fun U hU=> by simp [hU,h.side x U hU]⟩
  · exact tsum_congr fun j=> Work.H03.reads_larger (h.intervals j) (h.flags j x) U V hp hv
  exact masked_reads B (F:=T.backs x) (fun U V he=> congrArg (T.factor • ·) ((h.stencils x) U V
    (agrees_mono he (Finset.coe_subset.mpr (h.boundLinks.trans (neighborhood_mono h.fits.le)))))) U V hp hv
lemma drift_gauge x : GaugeInvariant (T.drift B x) := by
  intro k U; unfold drift; exact congrArg₂ Sub.sub (tsum_congr fun j=> h.sectors j x k U) (masked_gauge _ _ _ (purchased h x).symmetry k U)
lemma drift_meas x : Measurable (T.drift B x) := by unfold drift; exact (Measurable.tsum fun j => h.meas j x).sub (masked_measurable _ _ _ (purchased h x).borel)

omit [Fintype V] in
lemma drift_bound (x : Cross X) (hx : UnitPage x) U : ‖T.drift B x U‖ ≤ T.tally := by
  by_cases hu:Healthy B.threshold T.plot U
  · rw [(drift_support h x).2 U hu,norm_zero]; exact budget_nonneg h.fee
  unfold drift; rw [Pi.sub_apply,masked_ne _ _ _ _ hu,sub_zero]
  have he:= h.fee.2.1.of_nonneg_of_le (fun j=>norm_nonneg _) (fun j=> h.costs x hx j U)
  exact (norm_tsum_le_tsum_norm he).trans ((he.tsum_le_tsum (fun j=> h.costs x hx j U) h.fee.2.1).trans h.fee.2.2)
end Crown
end YM.Comparison.Density.Convert
