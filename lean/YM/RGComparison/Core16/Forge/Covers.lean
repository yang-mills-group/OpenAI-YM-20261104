import YM.RGComparison.Core16.Barrier
import YM.Gauge.Size
import YM.Push.ABSOLUTE_SUMS.Animals

/-!
# Period/copy-count uniform primitive step matching. Local exchange gas criterion, compact group.

Site coordinates fine after blocking. Main handles Peierls displacement replacement with no-hole
external field V in its post-block *global* near-flat fluctuation-ray domain (thresholded coarse links,
not just healthy flags). Internal suppull estimates via translating distances at transition. All tags
joint, integrated before the estimator. `Meets`: permit likelihood discontinuity even after replacing ALL
link variables in any specific neighborhood. Preserve all costs exactly sufficiently far from there
using common TAG coupling. Not a normalized-likelihood-ratio assumption nor an assumption needing
simultaneous support on a free real posterior product! See `Exchange` for specialization on
Wilson kernels. Sequencing costs include unmarked (extensive), forced, Markov noise, Jacobian and
posterior normalization; identities in respective bindings (this is on whole-path cost, not estimation
in individual Rep-partners).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Forge
open Filter Function Finset Lattice RG Tree Wilson MeasureTheory Push.AbsoluteSums.Animals
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge} {S : Side} {ι k T : Type} [Fintype ι] [Fintype k] [Fintype T]

def neighborsOf (loc:ι→Site S) (m:ℕ) (z:Site S):= Finset.univ.filter fun i=>separation z (loc i) ≤ m
lemma member (loc:ι→Site S) (m:ℕ) (z:Site S) {i:ι} : i∈neighborsOf loc m z ↔ separation z (loc i)≤m:=by simp [neighborsOf]

def Coverage (K : ℕ) (loc:ι→Site S) := ∀ z:Site S, (Finset.univ.filter fun i=> loc i=z).card ≤ K
lemma price_cover {loc:ι→Site S}{K:ℕ}(h: Coverage K loc) (m:ℕ)(z: Site S):(neighborsOf loc m z).card ≤ ballCost m*K:=by
    let t (p: Site S) := Finset.univ.filter fun i=> loc i=p
    let E:= neighbors m z
    have he: neighborsOf loc m z ⊆ E.biUnion t:=fun i hi=>mem_biUnion.mpr ⟨_,(neighbors_mem ..).mpr ((member ..).1 hi),mem_filter.mpr ⟨mem_univ _,(show loc i=_ from rfl)⟩⟩
    refine ((card_le_card he).trans (card_biUnion_le)).trans ((sum_le_sum (f:=fun p=> (t p).card) (g:=fun _=> K) (fun i _=>h i)).trans ?_)
    rw [sum_const,smul_eq_mul]; exact Nat.mul_le_mul_right _ (neighbors_card m z)

lemma further (loc:ι→ Site S) {u v m z}{x}(h:x∈neighborsOf loc m v)(hv:separation u v ≤ z): x∈neighborsOf loc (z+m) u:=
    (member ..).2 ((separation_triangle _ _ _).trans <| Nat.add_le_add hv ((member ..).1 h))

lemma enlarged (loc:ι→Site S) (z:Site S) : Monotone fun m=> neighborsOf loc m z := fun _ _ hh _ hx => (member ..).2 (((member ..).1 hx).trans hh)

-- cost of overlapping near-energy readbacks.
lemma window_cost {x: ι→ Site S}(y:k→Site S){K : ℕ}(w:Coverage K x) (F:k→ℝ)(hF:∀i, 0≤ F i) (z:Site S) (R b:ℕ) :
    ∑ i∈neighborsOf x R z, ∑ j∈neighborsOf y b (x i), F j ≤
        (ballCost b * K:ℕ)* ∑ j∈neighborsOf y (R+b) z, F j := by
    let I := neighborsOf x R z; let J:= neighborsOf y (R+b) z
    have he (i:ι) (hi:i∈I): ∑ j∈neighborsOf y b (x i), F j = ∑ j∈J, if i∈neighborsOf x b (y j) then F j else 0:=by
       rw [←sum_filter]; congr 1; ext p; rw [mem_filter]; constructor
       · intro h; refine ⟨further _ h ((member ..).1 hi), (member ..).2 ?_⟩; rw [separation_comm]; exact (member ..).1 h
       intro h; rw [member,separation_comm]; exact (member ..).1 h.2
    rw [sum_congr (s₁:=I) rfl he, sum_comm, mul_sum]; refine sum_le_sum fun j _ => ?_
    rw [←sum_filter, sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ (hF _); exact Nat.cast_le.mpr <| (card_le_card (show I.filter (fun i=>i∈neighborsOf x b (y j)) ⊆ _ from fun i hi=> (mem_filter.mp hi).2)).trans (price_cover w b _)

abbrev Sky (G:Gauge)(ι:Type):=ι→ G.El

def skillet (G:Gauge)(ι:Type)[Fintype ι] : Measure (Sky G ι):= Measure.pi fun _=> G.probHaar
instance : IsProbabilityMeasure (skillet G ι):= by unfold skillet; infer_instance

def nib (x:Sky G ι) (i:ι) := G.chord (x i)^2

-- Tags joined with pointwise marginals.
structure Glued (μ ν:T→ℝ) (M:T→T→ℝ):Prop where
  pos i j : 0 ≤ M i j
  west i : ∑ j,M i j=μ i
  east j : ∑ i,M i j=ν j

structure Base (G:Gauge) (S:Side) (ι k T:Type) where
    loc : ι→ Site S
    band : k→Site S
    choices : T→Sky G ι→ℝ
    cost : T→Sky G ι→ k→ℝ

structure Prices where
    b : ℕ
    K : ℕ
    D : ℝ
    K_pos : 0<K
    D_pos : 0<D

namespace Base
variable (B:Base G S ι k T)(X:Prices)

def action (s:T)(x:Sky G ι) := ∑ j,B.cost s x j

def cash (s:T)(g:ℝ)(x:Sky G ι):=Real.exp (-(B.action s x)/g^2)
def output (g:ℝ)(x:Sky G ι):= ∑ t,B.choices t x*B.cash t g x

def Meets (b:ℕ):Prop:=∀ (z:Site S)(x y:Sky G ι)(R:ℕ), (∀ i∉neighborsOf B.loc R z, x i=y i) →
  ∃ M:T→T→ℝ, Glued (Function.swap B.choices x) (Function.swap B.choices y) M ∧ ∀ i j,0<M i j→∀ a∉neighborsOf B.band (R+b) z, B.cost i x a=B.cost j y a

structure Admits (g:ℝ):Prop where
    pos (x:Sky G ι) (t:T): 0≤B.choices t x
    normalized (x:Sky G ι): ∑ t,B.choices t x=1
    meas (t:T) : Measurable (B.choices t)
    generates (x:Sky G ι) (t:T) (j:k): 0≤ B.cost t x j
    wires (t:T)(j:k): Measurable (fun x=> B.cost t x j)
    core : Coverage X.K B.loc
    edge : Coverage X.K B.band
    min (x:Sky G ι) (t:T) (i:ι): 0< B.choices t x →
      nib x i ≤ X.D * (g^2 + ∑ j∈neighborsOf B.band X.b (B.loc i), B.cost t x j)
    max (x:Sky G ι) (t:T) (j:k): 0< B.choices t x →
      B.cost t x j ≤ X.D * (g^2 + ∑ i∈neighborsOf B.loc X.b (B.band j), nib x i)
    glue : B.Meets X.b

variable {B X} {g:ℝ}(H:B.Admits X g)
omit [Fintype ι] in
lemma nib_nonneg (x:Sky G ι)(i:ι): 0≤ nib x i:=sq_nonneg _
omit [Fintype ι] [Fintype T] in
lemma cash_pos (t:T)(x:Sky G ι):0<B.cash t g x:=Real.exp_pos _
include H
lemma output_pos (x:Sky G ι):0<B.output g x:=by
    have hx:= H.normalized x; have hQ : 0 < ∑ t,B.choices t x:=hx ▸ zero_lt_one
    obtain ⟨i,h⟩:= Finset.sum_pos_iff_of_nonneg (fun i _ => H.pos x i) |>.1 hQ
    exact (Finset.sum_pos_iff_of_nonneg (fun i _=>mul_nonneg (H.pos x i) (cash_pos ..|>.le))).2 ⟨i,mem_univ _,mul_pos h.2 (cash_pos ..)⟩
lemma output_le (x : Sky G ι) : B.output g x ≤ 1:=by
    refine (sum_le_sum (f:=fun i=>_) (fun i _=> mul_le_of_le_one_right (H.pos x i) (show B.cash i g x ≤ 1 from ?_))).trans_eq (H.normalized x)
    unfold cash; rw [Real.exp_le_one_iff]; exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sum_nonneg fun j _=> H.generates x i j)) (sq_nonneg _)
lemma output_env : Envelope (B.output g):=by
    refine ⟨?_,1,fun i=> (Real.norm_of_nonneg (output_pos H i|>.le)).le.trans (output_le H i)⟩
    unfold output; refine Finset.measurable_fun_sum _ fun i _=> (H.meas i).mul ?_
    unfold cash action; exact Real.continuous_exp.measurable.comp ((Finset.measurable_fun_sum _ fun j _=> H.wires i j).neg.div_const _)

end Base
end YM.RGComparison.Core16.Forge
