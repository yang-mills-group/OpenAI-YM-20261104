import YM.Comparison.Density.Payload.Registers
/-!
This expansion object has a single vacuum and full markers. Its log
part is reconstructed from masked registers; the forced part from the
actual selected gas. Parts of `Support`, even if used only on the held
field, must be inherited (cf UsesFinal for flags). All cost predicates
are on ACTUAL coefficients before summing over addresses. This includes
asking for test *sup* bounds per address, not existential choices of
envelopes after tests. We construct deterministic merged addresses later.

No lower-order affine/scalar/resets or coordinates inferred from this
type. `Fine` doesn't assert the vacuum Lawful or any gauge/analytic
budget for it; it describes the marked extension. `Vac` in Boot later
owns vacuum assertions.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density
open Marker Testing Markers RG Lattice Function MeasureTheory Wilson Filter
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical
variable {V : Type} [DecidableEq V] {R : Census V} {G : Gauge} {n : Side}
variable {X : V→Type} [∀ v, NormedAddCommGroup (X v)] [∀ v, NormedSpace ℂ (X v)]

structure Assembly (R : Census V) (X : V→Type) (G : Gauge) (n : Side) where
  exponent : Registers R X G n
  arms : Cross X → Supply R G n

def Deposits (p : BudgetPoint) (w : V→ℝ) (O : Origin V n) (s : ℕ→ Support n) (F : Cross X→Supply R G n) (e b : ℝ) :=
    ∃ c : ℕ→ Poly R, (∀ x, UnitPage x → ∀ i U, Over (F x i U) (c i)) ∧
      (∀ i,Carries O.uses (s i) (c i)) ∧ Ac.Hit s p.B (Poly.price w ∘ c) (p.supportExponent+e) b

def Account (p : BudgetPoint) (w : V→ℝ) (O : Origin V n) (s : ℕ→ Support n) (F : Cross X→Supply R G n) (κ b : ℝ) :=
    0 < κ ∧ ∃ c : ℕ→ Poly R, (∀ x, UnitPage x → ∀ i U, Over (F x i U) (c i)) ∧
      (∀ i,Carries O.uses (s i) (c i)) ∧ ∀ i : V,
        SumBudget (fun l : ℕ=>κ⁻¹ * p.mass (s l) (∑ j : R.Mode,if i∈j.val then Poly.toll w j * ‖(c l).part j‖ else 0)) b

variable {O : Readers V X n} {w : V→ℝ} {P : Rep G n} {Q : Assembly R X G n} {p : BudgetPoint}
variable {c b k e : ℝ}

-- normalize test costs only to justify unconditional series. Estimate NOT used in propagation.
section
variable (hw : ∀ i,0<w i) (hk : 0≤ e)
variable {s : ℕ→ Support n} {F : Cross X→ Supply R G n}
include hw hk
lemma Deposits.pay (ht : ∀ i,(s i).Nonempty) (h : Deposits p w O.source s F e k) [Fintype V]
    (he : ∀ i U, Catalogue O.locus (s i) (fun x=> F x i U)) (x : Cross X) :
    ∃ a : ℕ→ℝ, (∀ i,0≤a i) ∧ Summable a ∧ ∀ i U, Poly.price w (F x i U) ≤ a i := by
  obtain ⟨v,y,hv,rfl⟩:= Testing.normalize x
  obtain ⟨d,hd,H,h⟩:=h
  have hh := Activities.summable_charge ht (fun i=> Poly.nonnegative hw _) (bound_plain (p:=p) hw e hk h)
  let m : ℝ := ∑ i : R.Mode, ‖v^i.val.card‖
  have hm : 0 ≤ m := Finset.sum_nonneg fun _ _=> norm_nonneg _
  refine ⟨fun i=>m*Poly.price w (d i),fun _=>mul_nonneg hm (Poly.nonnegative hw _), hh.mul_left m,fun i U=> ?_⟩
  apply le_trans _ (mul_le_mul_of_nonneg_left ((hd y hv i U).price hw) hm)
  unfold Poly.price; rw [Finset.mul_sum]; refine Finset.sum_le_sum fun j _=>?_
  have hq : ‖v^j.val.card‖ ≤ m:= Finset.single_le_sum (f:=fun i : R.Mode=> ‖v^i.val.card‖) (fun _ _=> norm_nonneg _) (Finset.mem_univ j)
  rw [show (F (v • y) i U).part j=_ from ((he i U).pieces j).stretch v y,norm_smul,mul_left_comm]
  exact mul_le_mul_of_nonneg_right hq (mul_nonneg (Poly.worth hw _).le (norm_nonneg _))

omit [∀ v, NormedSpace ℂ (X v)] in
lemma Deposits.vac (H : ∀ x, Manifest (Q.arms x) P.activities P.p O.source)
    (h : Deposits P.p w O.source (ranges P.activities) Q.arms e k) : P.activities.KBound P.p k := by
  obtain ⟨d,hd,hq,h⟩:=h
  exact vacuum_bound _ hw hk (H 0) ⟨d,hd 0 (fun i=> by simp),hq,h⟩
omit [∀ v, NormedSpace ℂ (X v)] in
lemma Deposits.rooted (h : Deposits P.p w O.source (ranges P.activities) Q.arms e k) {κ : ℝ} (hκ : 0 < κ) :
    Account (later P.p e hk) w O.source (ranges P.activities) Q.arms κ (k/κ) := by
  obtain ⟨d,hd,hq,h⟩:=h
  have hp : Ac.Hit (ranges P.activities) (later P.p e hk).B (Poly.price w ∘ d) ((later P.p e hk).supportExponent+0) k:= by simpa only [later,add_zero] using h
  exact ⟨hκ,d,hd,hq,fun i=> divide_fixed hw (t:=0) le_rfl hκ d hq hp i⟩
end

namespace Assembly
structure Fine (P : Rep G n) (O : Readers V X n) (Q : Assembly R X G n) : Prop where
  layout : Q.exponent.Layout P.p O
  carries x : Manifest (Q.arms x) P.activities P.p O.source
  tickets i U : Catalogue O.locus (ranges P.activities i) (fun x=> Q.arms x i U)

structure Tidy (P : Rep G n) (w : V→ℝ) (O : Readers V X n) (Q : Assembly R X G n) (c b e k : ℝ) : Prop extends Fine P O Q where
  growth : Q.exponent.Budget P.p O w c b
  bill : Deposits P.p w O.source (ranges P.activities) Q.arms e k

variable [Fintype V]

def eval (P : Rep G n) (Q : Assembly R X G n) (x : Cross X) (U : Config G n) :=
    magnify (P.exponent U) (Q.exponent.log P.p x U) * mist P.p P.activities (Q.arms x) U

variable (hw : ∀ i,0<w i) (hk : 0≤e) (h : Tidy P w O Q c b e k)

include hw hk h
lemma raw (x : Cross X) : ∃ a : ℕ→ℝ, (∀ i,0≤a i) ∧ Summable a ∧ ∀ i U,Poly.price w (Q.arms x i U) ≤ a i:=
    h.bill.pay hw hk (fun i=> (P.activities.forced i).inventory_ne.mono (P.activities.forced i).inventory_sup) h.tickets x
lemma force_dom (x : Cross X) : RG.Dominated (packet P.p P.activities (Q.arms x)):= by
  obtain ⟨a,ha,hf,H⟩:= raw hw hk h x; let f (i:Finset ℕ):=∏ j∈i,a j
  obtain ⟨m,hm,hX⟩:= Poly.equivalent_norm (R:=R) hw
  refine ⟨fun i=> f i * m, (summable_finsetProd_of_summable_nonneg ha hf).mul_right m,fun i U=> (hX _).trans (mul_le_mul_of_nonneg_right ?_ hm)⟩
  unfold packet; split
  · exact (Poly.multiple hw ..).trans (Finset.prod_le_prod (fun _ _=> Poly.nonnegative hw _) fun _ _=> H ..)
  rw [Poly.zero_price]; exact Finset.prod_nonneg fun _ _=> ha _

lemma literal (x : Cross X) (U : Config G n) :
    (mist P.p P.activities (Q.arms x) U).part R.quiet=(P.activities.gas P.p U:ℂ):= by
  have hh (b : Finset ℕ) : (packet P.p P.activities (Q.arms x) b U).part R.quiet= (P.activities.gasOccurrence P.p b U:ℂ) := by
    unfold packet Activities.gasOccurrence; split
    · rw [Multi.quiet_of_prod,Complex.ofReal_prod]; exact Finset.prod_congr rfl fun i _=> (h.carries x).quiet i U
    simp
  unfold mist Activities.gas; rw [Poly.share ((force_dom hw hk h x).summable U)]; simp_rw [hh]
  rw [Complex.ofReal_tsum]
lemma zero_order (x : Cross X) (U : Config G n) :
    (Q.eval P x U).part R.quiet=(P.eval U:ℂ) := by
  rw [eval,magnify,Poly.quiet_mul, literal hw hk h, Poly.quiet_mul, embedded_part, Poly.pass_part _ (Registers.baseline _ _),Rep.eval]; simp
lemma production (U : Config G n) : Catalogue O.locus Finset.univ (fun x=> Q.eval P x U):= by
  have hx : Catalogue O.locus Finset.univ (fun x=> mist P.p P.activities (Q.arms x) U):= by
    have he b : Catalogue O.locus Finset.univ (fun x=> packet P.p P.activities (Q.arms x) b U) := by
      unfold packet; by_cases hd : P.activities.admissible P.p U b
      · simp only [if_pos hd]; exact Catalogue.prod _ _ (fun i _=> (h.tickets i U).roomier (Finset.subset_univ _))
      simp only [if_neg hd]; exact Catalogue.empty
    have ha (j : R.Mode) (x : Cross X) : (mist P.p P.activities (Q.arms x) U).part j=
        ∑' b,(packet P.p P.activities (Q.arms x) b U).part j := Poly.share ((force_dom hw hk h x).summable U) _
    refine ⟨fun i=>?_,fun i x y H=>?_⟩
    · simp_rw [ha]; exact Slotted.series _ (fun b=> (he b).pieces i) fun x => (((force_dom hw hk h x).summable U).hasSum.map (Poly.get i) (Poly.get i).continuous).summable
    dsimp only; rw [ha i x,ha i y]; exact tsum_congr fun b=> (he b).track i x y H
  exact ((Catalogue.pegged _).times (Catalogue.soaring (Registers.complete_reads hw h.layout h.growth U))).times hx

end Assembly
end YM.Comparison.Density
