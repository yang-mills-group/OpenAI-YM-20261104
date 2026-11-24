import YM.Comparison.RG02.Bulk.Sequence
import YM.Next.MULTISOURCE.Measure
import YM.Push.GRID_APPROXIMATION.Bounds
import YM.Push.SECTOR_MEASURE.Bounds
import YM.Push.SECTOR_MEASURE.Gauges
import YM.Push.BETA_TRANSPORT.Noise
/-!
# Exact charging convention

State the marker table all-good etc using Leaf.All. No Poly norm Eq across censuses beyond
 the algebraic claims (Fintype finite on actual markers). Use `prior`, `F.order`, etc exact measure
 conventions; each theorem requiring complex compatibility asks for L¹ of **every entry it uses**.
 Conversions between normalized/unmarked, integral, etc distinguished. This module binds
 `Tagged` expectation before any source-dependent branch conditioning. No insertion evaluated in
 different V or independent tag for a repeated read.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Actual
open Function Filter Finset MeasureTheory
open RG Precision Lattice Wilson Exterior Tree YM.Push.SectorMeasure
open YM.Marker YM.Multi Order
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
    {V : Type} [DecidableEq V] {R : Census V}
variable {X : Type*}
abbrev Lit (R : Census V) (X : Type*) := X→Poly R
abbrev atMark (s : R.Mode) (D : Lit R X) : X→ℂ := fun x=> (D x).part s

section integration
variable [MeasurableSpace X] (μ : Measure X)
def Good (D : Lit R X) := ∀ s, Integrable (atMark s D) μ
def charge (D : Lit R X) := Poly.inject (fun s=> ∫ x,atMark s D x ∂μ)
lemma components (s : R.Mode) (D : Lit R X) : (charge μ D).part s=∫ x,atMark s D x ∂μ := rfl
lemma Good.of_bound [IsFiniteMeasure μ] {D : Lit R X} (h : Leaf.All D) : Good μ D := fun i=> (h i).integrableC _
omit [MeasurableSpace X] in
@[simp] lemma mark_add (D D' : Lit R X) (t : R.Mode) : atMark t (D+D')=atMark t D + atMark t D' := rfl
omit [MeasurableSpace X] in
@[simp] lemma mark_sub (D D' : Lit R X) (t : R.Mode) : atMark t (D-D')=atMark t D - atMark t D':= by funext x; change (D x-D' x).part t=_; rw [← show ∀a b:Poly R, a+-b=a-b from fun a b=> (sub_eq_add_neg a b).symm,Poly.part_plus,Poly.part_neg]; exact (sub_eq_add_neg ..).symm
omit [MeasurableSpace X] in
@[simp] lemma mark_smul (D : Lit R X) (t : R.Mode) (z : ℂ) : atMark t (z•D)=z•atMark t D:=rfl
omit [MeasurableSpace X] in
lemma mark_cut {Y : Set X} (D : Lit R X) (t : R.Mode) : atMark t (Y.indicator D)=Y.indicator (atMark t D) := by unfold atMark; ext1 x; by_cases h:x∈Y<;> simp [*,Poly.part_nil]
variable {μ} {D D' : Lit R X} {Y : Set X}
lemma Good.add (h : Good μ D) (hn : Good μ D') : Good μ (D+D') := by simp_rw [Good,mark_add]; exact fun i=> (h i).add (hn i)
lemma Good.sub (h : Good μ D) (hn : Good μ D') : Good μ (D-D') := by simp_rw [Good,mark_sub]; exact fun i=> (h i).sub (hn i)
lemma Good.const_mul (h : Good μ D) (z : ℂ): Good μ (z•D) := fun i=> (h i).const_mul z
lemma Good.on_window (h : Good μ D) (hm : MeasurableSet Y) : Good μ (Y.indicator D) := by simp_rw [Good,mark_cut]; exact fun i=> (h i).indicator hm
lemma Good.within (h : Good μ D) (s : Set X) : Good (μ.restrict s) D := fun i=> (h i).integrableOn
lemma Good.sum {I : Type*} (F : Finset I) {X' : I → Lit R X} (h : ∀ i∈F, Good μ (X' i)) : Good μ (∑ i∈F,X' i) := by
  intro i; unfold atMark; simp_rw [Finset.sum_apply,Poly.part_sum]; exact integrable_finsetSum _ (fun j hj=>h j hj i)
lemma Covered (h : Leaf.All D) (hm : MeasurableSet Y) : Leaf.All (Y.indicator D) := Leaf.trigger _ hm h
lemma leaf_sub (h : Leaf.All D) (h' : Leaf.All D') : Leaf.All (D-D') := fun x=> by change Envelope (atMark x (D-D')); rw [mark_sub]; exact (h x).subC (h' x)
lemma add_cost (h : Good μ D) (hn : Good μ D') : charge μ (D+D')=charge μ D+charge μ D' := by
   ext i; rw [Poly.part_plus,components, mark_add]; exact integral_add (h i) (hn i)
lemma sub_cost (h : Good μ D) (hn : Good μ D') : charge μ (D-D')=charge μ D-charge μ D' := by
   rw [eq_sub_iff_add_eq, ← add_cost (h.sub hn) hn,sub_add_cancel]
lemma smul_cost (z : ℂ) : charge μ (z•D)=z • charge μ D := Poly.ext fun i=> integral_const_mul z (atMark i D)
lemma sum_cost {I : Type*} (F : Finset I) {X' : I→Lit R X} (h : ∀ i∈F,Good μ (X' i)) : charge μ (∑ i∈F,X' i)=∑ i∈F,charge μ (X' i) := by
   ext i; rw [Poly.part_sum,components]; unfold atMark; simp_rw [Finset.sum_apply,Poly.part_sum]; exact integral_finsetSum _ (fun j hj=> h j hj i)

lemma restricted_cost (h : MeasurableSet Y) (D : Lit R X) : charge (μ.restrict Y) D=charge μ (Y.indicator D) := by
   ext i; rw [components, components, mark_cut, integral_indicator h]
lemma split_cost (h : Good μ D) (he : MeasurableSet Y) : charge μ D=charge μ (Y.indicator D)+charge μ (Yᶜ.indicator D) := by
   rw [← add_cost (h.on_window he) (h.on_window he.compl), Set.indicator_self_add_compl]
lemma parallel (h : D =ᵐ[μ] D') : charge μ D=charge μ D' := Poly.ext fun i=> integral_congr_ae (h.mono fun _ hz=> congrArg (Poly.part · i) hz)
lemma Good.parallel (h : D =ᵐ[μ] D') : Good μ D ↔ Good μ D' := by unfold Good; exact forall_congr' fun i=> integrable_congr (h.mono fun _ hz=> congrArg (Poly.part · i) hz)
end integration

variable (F : Forest S.ratio) (t : S.Choices) (D : Lit R (Config G f)) (J : Config G c) (β : ℝ)
variable (S) in
def Push (b : Lit R (Config G f)) (V' : Config G c) :=
    charge (prior G f) (fun U=> Complex.ofReal (S.density β U V') • b U)
-- often easier to read directing powers
lemma grades : (Push S β D J).part= fun s => S.push β (atMark s D) J := by
   funext s; unfold Push; rw [components]; unfold atMark; simp_rw [Poly.part_smul]; unfold StepData.push; simp [Complex.real_smul]

variable {D}
-- tagged windows separately admitting different forest F from an explicit finite law later.
def stack (D : Lit R (Config G f)) (U : Config G f) := Complex.ofReal (taggedKernel S β t U J) • D U
lemma tall (ok : S.patch.Branches S.kernel G) (h : Leaf.All D) : Leaf.All (stack t J β D) := Leaf.smul (Envelope.ofReal_env (env_tagged β t ok measurable_id measurable_const)) h
lemma collective (D : Lit R (Config G f)) : (fun x=>Complex.ofReal (S.density β x J) • D x)=∑ t : S.Choices, stack t J β D := by
  ext x i
  simp [stack, StepData.density, Poly.part_sum, Finset.sum_apply, Finset.sum_mul,taggedKernel]
lemma agreed (ok : S.patch.Branches S.kernel G) (h : Leaf.All D) : Push S β D J = ∑ t : S.Choices, charge (prior G f) (stack t J β D) := by rw [Push,collective _ _ D,sum_cost]; exact fun i _=> Good.of_bound _ (tall i J β ok h)
lemma stack_rooted {D' : Lit R (Config G f)} (H : S.patch.Branches S.kernel G) (k : Site f→G.El) (h : ∀ i : Site c,k (S.ratio.embed i)=1) (hm : GaugeInvariant D') (U : Config G f) : stack t J β D' (gauge k U)=stack t J β D' U := by
   unfold stack taggedKernel; obtain ⟨he,hv⟩:= choice_gauge H U t k; rw [he,hv, hm]; rw [show Lattice.gauge (k ∘ S.ratio.embed) (S.prediction U t)=S.prediction U t by funext e; simp [Lattice.gauge,h]]
lemma pack (ok : S.patch.Branches S.kernel G) (h : Leaf.All D) (hg : GaugeInvariant D) : charge (prior G f) (stack t J β D)=charge (F.order G) (stack t J β D∘F.drape) := by
   ext i; exact F.pack _ (Good.of_bound _ (tall t J β ok h) i) (fun k hx y=> congrArg (Poly.part · i) (stack_rooted t J β ok k hx hg y))
lemma good_slice (ok : S.patch.Branches S.kernel G) (h : Leaf.All D) : Good (F.order G) (stack t J β D∘F.drape) := Good.of_bound _ fun i=> ((tall t J β ok h) i).comp_env F.continuous_drape.measurable
end YM.Comparison.RG02.Actual
