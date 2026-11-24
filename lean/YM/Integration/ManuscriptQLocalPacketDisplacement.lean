import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Polynomial.Eval.Degree
import YM.Integration.ManuscriptQLocalActualLog
import YM.Integration.ManuscriptQLocalEffectiveInput
import YM.Comparison.RG02.Valence.Amplify
import YM.Comparison.RG02.Assembly.Kernel
import YM.Comparison.RG02.Laplace.Trunc
import YM.Comparison.RG02.Integral.Bill
import YM.Comparison.RG02.Laplace.Fleet

/-!
# Displacing the actual packet field and its physical conditional

At the true cutoff the countable original packet read, its finite nilpotent
exponential and its spatially integrated normalized connected logarithm have
finite degree in the auxiliary displacement. The same input fields and the
same quiet denominator occur across all phases.
-/

set_option autoImplicit false
noncomputable section

section
/-! Finite unit-source reconstruction for the charged Wilson table. The
normalization is the total variation of a *single* coefficient, before
the number of regulators, sources or Wilson fields is selected. -/
namespace YM.Integration.ManuscriptQLocalSourceFourier
open Finset
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A unit source at each of the D+1 sample points. The unmodulated
physical source is the sample j=0. -/
def phase {D : ℕ} (j : ZMod (D+1)) : ℂ := ZMod.stdAddChar (-j)

theorem unit {D : ℕ} (j : ZMod (D+1)) : ‖phase j‖=1 := by
  simp only [phase,ZMod.stdAddChar_apply,Circle.norm_coe]

@[simp] theorem first (D : ℕ) : phase (0:ZMod (D+1))=1 := by simp [phase]

/-- Exact complex weight of one measured unit-phase sample in the kth
displacement coefficient. -/
def weight {D : ℕ} (j k : ZMod (D+1)) : ℂ :=
  ((D+1:ℕ):ℂ)⁻¹*ZMod.stdAddChar (j*k)

def project {D : ℕ} (u : ZMod (D+1)→E) (k : ZMod (D+1)) : E :=
  ZMod.dft.symm u k

theorem projection {D : ℕ} (u : ZMod (D+1)→E) (k : ZMod (D+1)) :
    project u k = ∑ j,weight j k • u j := by
  rw [project,ZMod.invDFT_apply,Finset.smul_sum]
  simp only [weight,smul_smul]

theorem variation {D : ℕ} (k : ZMod (D+1)) : ∑ j,‖weight j k‖=1 := by
  have h : ((D+1:ℕ):ℝ)≠0 := by positivity
  simp only [weight,norm_mul,norm_inv,ZMod.stdAddChar_apply,Circle.norm_coe,mul_one,
    Complex.norm_natCast,Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul,mul_inv_cancel₀ h]

/-- Every signed discrepancy in the genuine sample portfolio retains
the original norm envelope, separately at each displacement. -/
theorem estimate {D : ℕ} (u v : ZMod (D+1)→E) {ε : ℝ}
    (h : ∀j,‖u j-v j‖≤ε) (k : ZMod (D+1)) :
    ‖project u k-project v k‖≤ε := by
  rw [projection,projection,←Finset.sum_sub_distrib]
  calc _ ≤ ∑ j, ‖weight j k‖*ε := by
            refine (norm_sum_le _ _).trans (sum_le_sum fun j _=>?_)
            rw [←smul_sub,norm_smul]
            exact mul_le_mul_of_nonneg_left (h j) (norm_nonneg _)
       _ = ε := by rw [←Finset.sum_mul,variation,one_mul]

theorem character {D : ℕ} (j k : ZMod (D+1)) :
    phase j^k.val = ZMod.stdAddChar (-(k*j)) := by
  rw [phase,←AddChar.map_nsmul_eq_pow,nsmul_eq_mul,ZMod.natCast_zmod_val,mul_neg]

/-- Coefficient projection on an arbitrary Banach-valued physical family
which was computed independently at the D+1 true phases. -/
theorem recover {D : ℕ} (a : ZMod (D+1)→E) (k : ZMod (D+1)) :
    project (fun j=>∑ l,phase j^l.val • a l) k = a k := by
  have h : (fun j=>∑ l,phase j^l.val • a l)=ZMod.dft a := by
    funext j
    simp only [ZMod.dft_apply,character]
  rw [h,project,LinearEquiv.symm_apply_apply]

/-- The independently selected effective output laws at auxiliary phases
exactly recombine to the original unmodulated response on the physical
fiber. They need not be chosen functorially as functions of the phase. -/
theorem measured {D : ℕ} (u : ZMod (D+1)→E) :
    ∑ k,project u k = u 0 := by
  have h := congrFun (ZMod.dft.apply_symm_apply u) (0:ZMod (D+1))
  simpa only [ZMod.dft_apply,mul_zero,neg_zero,AddChar.map_zero_eq_one,one_smul,project] using h

/-- For a positive or negative signed measured coupling, restore the
stored output Laurent powers at the exact same physical value. -/
theorem restored {D : ℕ} (u : ZMod (D+1)→E) {g : ℂ} (hg : g≠0) :
    ∑ k, g^k.val • ((g^k.val)⁻¹ • project u k)=u 0 := by
  simp only [smul_smul,mul_inv_cancel₀ (pow_ne_zero _ hg),one_smul,measured]

/-- Numerical samples of the actual scalar generator compute its literal
polynomial coefficients. This also addresses vanishing powers. -/
theorem polynomial {D : ℕ} (p : Polynomial ℂ) (h : p.natDegree≤D) (k : ZMod (D+1)) :
    project (fun j=>p.eval (phase j)) k=p.coeff k.val := by
  apply Eq.trans _ (recover (fun i : ZMod (D+1)=>p.coeff i.val) k)
  apply congrArg (fun u=>project u k)
  funext j
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le h)]
  change _ = ∑ i : Fin (D+1),phase j^i.val • p.coeff i.val
  calc
    _ = ∑ i : Fin (D+1),p.coeff i.val*phase j^i.val :=
      (Fin.sum_univ_eq_sum_range (fun i:ℕ=>p.coeff i*phase j^i) (D+1)).symm
    _ = _ := Finset.sum_congr rfl fun _ _=>mul_comm _ _

end YM.Integration.ManuscriptQLocalSourceFourier
end

section
/-! Polynomial dependence on independent unit-source phases. A nonempty
true mark may spend the shift attached to it once. The extra variables
used by the Wick coefficient extraction may all have weight zero. -/
namespace YM.Integration.ManuscriptQLocalShiftLedger
open Finset Marker Multi
open Comparison.RG02 Cumulants Extra.Trajectories
open scoped Classical BigOperators

variable {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}

def weight (w : V→ℕ) (s : Γ.Mode) : ℕ := ∑ v∈s.val,w v

def Ledger (w : V→ℕ) (u : ℂ→Poly Γ) : Prop :=
  ∀s,∃ p : Polynomial ℂ,p.natDegree ≤ weight w s ∧ ∀z,p.eval z = (u z).part s

omit [Fintype V] in
private theorem join (w : V→ℕ) {i j s : Γ.Mode} (h : Poly.merges i j s) :
    weight w i + weight w j = weight w s := by
  unfold weight
  rw [←h.2,sum_union h.1]

theorem degree_sum {α : Type*} (t : Finset α) (p : α→Polynomial ℂ) (c : ℕ)
    (h : ∀i∈t,(p i).natDegree≤c) : (∑ i∈t,p i).natDegree≤c := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    rw [sum_insert hi]
    exact Polynomial.natDegree_add_le_of_degree_le (h i (mem_insert_self _ _))
      (ih (fun j hj=>h j (mem_insert_of_mem hj)))

theorem eval_sum {α : Type*} (t : Finset α) (p : α→Polynomial ℂ) (z : ℂ) :
    (∑i∈t,p i).eval z = ∑i∈t,(p i).eval z :=
  map_sum (Polynomial.evalRingHom z) _ _

namespace Ledger
variable {w : V→ℕ} {u v : ℂ→Poly Γ}

omit [Fintype V] in
theorem constant (a : Poly Γ) : Ledger w (fun _=>a) :=
  fun s=>⟨Polynomial.C (a.part s),by simp,fun _=>Polynomial.eval_C⟩

omit [Fintype V] in
theorem add (hu : Ledger w u) (hv : Ledger w v) : Ledger w (fun z=>u z+v z) := by
  intro s
  obtain ⟨p,hp,hpz⟩ := hu s
  obtain ⟨q,hq,hqz⟩ := hv s
  exact ⟨p+q,Polynomial.natDegree_add_le_of_degree_le hp hq,fun z=>by
    rw [Polynomial.eval_add,hpz,hqz];rfl⟩

omit [Fintype V] in
theorem smul (c : ℂ) (hu : Ledger w u) : Ledger w (fun z=>c • u z) := by
  intro s
  obtain ⟨p,hp,hpz⟩ := hu s
  refine ⟨Polynomial.C c * p,?_,fun z=>by rw [Polynomial.eval_mul,Polynomial.eval_C,hpz];rfl⟩
  exact Polynomial.natDegree_mul_le.trans (by simp; exact hp)

omit [Fintype V] in
theorem sub (hu : Ledger w u) (hv : Ledger w v) : Ledger w (fun z=>u z-v z) := by
  simpa only [neg_one_smul,sub_eq_add_neg] using hu.add (smul (-1) hv)

omit [Fintype V] in
theorem sum {α : Type*} (t : Finset α) (a : α→ℂ→Poly Γ) (ha : ∀i,Ledger w (a i)) :
    Ledger w (fun z=>∑i∈t,a i z) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (constant (w:=w) (0:Poly Γ))
  | @insert i t hi ih => simpa only [sum_insert hi] using (ha i).add ih

omit [Fintype V] in
/-- The bound on a product is the sum over the *actual disjoint labels in
that surviving mode*, even before summing any spatial source locations. -/
theorem mul (hu : Ledger w u) (hv : Ledger w v) : Ledger w (fun z=>u z*v z) := by
  choose a ha ea using hu
  choose b hb eb using hv
  intro s
  let f := fun i j : Γ.Mode=>if h : Poly.merges i j s then a i*b j else 0
  have hf (i j) : (f i j).natDegree≤weight w s := by
    by_cases h : Poly.merges i j s
    · simp only [f,dif_pos h]
      exact Polynomial.natDegree_mul_le.trans ((Nat.add_le_add (ha i) (hb j)).trans_eq (join w h))
    · simp [f,h]
  refine ⟨∑i,∑j,f i j,degree_sum _ _ _ (fun i _=>degree_sum _ _ _ (fun j _=>hf i j)),?_⟩
  intro z
  rw [eval_sum,Poly.part_mul]
  refine sum_congr rfl fun i _=>?_
  rw [eval_sum]
  refine sum_congr rfl fun j _=>?_
  by_cases h : Poly.merges i j s <;> simp [f,h,ea,eb]

omit [Fintype V] in
theorem power (hu : Ledger w u) (k : ℕ) : Ledger w (fun z=>u z^k) := by
  induction k with
  | zero => simpa only [pow_zero] using (constant (w:=w) (1:Poly Γ))
  | succ k ih => simpa only [pow_succ] using ih.mul hu

theorem pass (hu : Ledger w u) : Ledger w (fun z=>Poly.pass (u z)) :=
  sum _ _ (fun i=>smul ((i.factorial:ℂ)⁻¹) (power hu i))

theorem connected (hu : Ledger w u) : Ledger w (fun z=>Extra.Trajectories.connected (u z)) := by
  have h (k) : Ledger w (fun z=>iteration (u z) k) := by
    induction k with
    | zero => exact constant 0
    | succ i hi => exact hi.add (hu.sub hi.pass)
  exact h (Fintype.card V)

omit [Fintype V] in
/-- The physically normalized denominator may be any fixed nonzero scalar.
The unit coupling phase changes only nonempty marked rows. -/
theorem normalized (hu : Ledger w u) {a : ℂ} (ha : ∀z,(u z).part Γ.quiet=a) :
    Ledger w (fun z=>Order.unitScale (u z)) := by
  have eq (z) : Order.unitScale (u z)=a⁻¹ • u z := by rw [Order.unitScale,ha]
  simpa only [eq] using smul a⁻¹ hu

end Ledger

omit [Fintype V] in
/-- Price a finite marked source from a bound on each full joint input
kernel. The charged generator need not have independent scalar slots. -/
theorem active {w : V→ℕ} (p : ℂ→Multi.Hot Γ→ℂ)
    (hp : ∀i : Multi.Hot Γ,∃q : Polynomial ℂ,q.natDegree≤weight w i.val ∧ ∀z,q.eval z=p z i) :
    Ledger w (fun z=>lit Γ (p z)) := by
  intro s
  by_cases h : s.val.Nonempty
  · obtain ⟨q,hq,he⟩ := hp ⟨s,h⟩
    exact ⟨q,hq,fun z=>(he z).trans (part_lit (p z) ⟨s,h⟩).symm⟩
  · obtain rfl := not_not.mp fun hn => h ((hot_iff_ne s).2 hn)
    exact ⟨0,by simp,fun z=>by rw [Polynomial.eval_zero,part_lit_quiet]⟩

end YM.Integration.ManuscriptQLocalShiftLedger
end

section
/-! Finite Fourier recovery of the marked degrees inside the original
measure. Each field point may supply its own polynomial witness. The
coefficients are recovered by finite signed measurements, which gives their
measurability and integrability on the very same field space. -/
namespace YM.Integration.ManuscriptQLocalShiftIntegral
open MeasureTheory Marker Multi Comparison.RG02
open ManuscriptQLocalShiftLedger
open scoped BigOperators Classical
namespace Fourier
open ManuscriptQLocalSourceFourier
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {D : ℕ}

def coefficient (u : ℂ→Ω→ℂ) (k : ZMod (D+1)) (a : Ω) :=
  project (fun i : ZMod (D+1)=>u (phase i) a) k

theorem integrable (u : ℂ→Ω→ℂ) (h : ∀i : ZMod (D+1),Integrable (u (phase i)) μ)
    (k : ZMod (D+1)) : Integrable (coefficient u k) μ := by
  change Integrable (fun a=>project (fun j : ZMod (D+1)=>u (phase j) a) k) μ
  simp only [projection,smul_eq_mul]
  exact integrable_finsetSum _ fun i _=>(h i).const_mul (weight i k)

theorem measured (u : ℂ→Ω→ℂ) (h : ∀i : ZMod (D+1),Integrable (u (phase i)) μ)
    (k : ZMod (D+1)) :
    project (fun i : ZMod (D+1)=>∫a,u (phase i) a ∂μ) k = ∫a,coefficient u k a ∂μ := by
  simp only [coefficient,projection,smul_eq_mul]
  rw [integral_finsetSum _ (fun i _=>(h i).const_mul (weight i k))]
  simp only [integral_const_mul]

theorem expanded (p : Polynomial ℂ) (hp : p.natDegree ≤ D) (z : ℂ) :
    p.eval z = ∑i : ZMod (D+1),p.coeff i.val*z^i.val := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp)]
  exact (Fin.sum_univ_eq_sum_range (fun j=>p.coeff j*z^j) (D+1)).symm

def collected (u : ℂ→Ω→ℂ) (μ : Measure Ω) (D : ℕ) : Polynomial ℂ :=
  ∑i : ZMod (D+1), Polynomial.C (∫a,coefficient u i a ∂μ) * Polynomial.X^i.val

theorem degree (u : ℂ→Ω→ℂ) (D : ℕ) : (collected u μ D).natDegree≤D := by
  apply degree_sum
  intro i _
  refine Polynomial.natDegree_mul_le.trans ?_
  simpa using (Nat.lt_succ_iff.mp i.val_lt)

theorem value (u : ℂ→Ω→ℂ) (h : ∀i : ZMod (D+1),Integrable (u (phase i)) μ)
    (located : ∀a,∃p : Polynomial ℂ,p.natDegree≤D ∧ ∀z,p.eval z=u z a) (z : ℂ) :
    (collected u μ D).eval z = ∫a,u z a ∂μ := by
  have almost (a : Ω) : u z a = ∑i : ZMod (D+1),coefficient u i a*z^i.val := by
    obtain ⟨p,hp,he⟩ := located a
    rw [← he,expanded p hp]
    apply Finset.sum_congr rfl
    intro i _
    have hi : coefficient u i a = p.coeff i.val := by
      simp only [coefficient,← he]
      exact polynomial p hp i
    rw [hi]
  rw [collected,eval_sum]
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  simp_rw [almost]
  rw [integral_finsetSum _ (fun i _=>(integrable u h i).mul_const (z^i.val))]
  simp only [integral_mul_const]

end Fourier

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} (w : V→ℕ)

omit [Fintype V] in
/-- The exact source degree survives a whole genuine finite Gibbs or
Gaussian integration. The original quiet measure may be arbitrary.
Only finitely many independently priced unit phases are used in each mode. -/
theorem charge (X : ℂ→Ω→Poly Γ) (hX : ∀u,Ledger w (fun z=>X z u))
    (hG : ∀z,Actual.Good μ (X z)) :
    Ledger w (fun z=>Actual.charge μ (X z)) := by
  intro s
  let f := fun z u => (X z u).part s
  exact ⟨Fourier.collected f μ (weight w s),Fourier.degree f (weight w s),fun z=>
    Fourier.value f (fun i=>hG _ s) (fun u=>hX u s) z⟩

/-- Division by the true common quiet and the finite connected logarithm
preserve the source degree on every mode, including its constant term. -/
theorem connected (X : ℂ→Ω→Poly Γ) (hX : ∀u,Ledger w (fun z=>X z u))
    (hG : ∀z,Actual.Good μ (X z)) (m : ℂ) (hm : ∀z,(Actual.charge μ (X z)).part Γ.quiet=m) :
    Ledger w (fun z=>Extra.Trajectories.connected (Order.unitScale (Actual.charge μ (X z)))) :=
  ((charge μ w X hX hG).normalized hm).connected

omit [Fintype V] in
/-- Formula for the actual coefficient of the whole normalized nonlinear
conditional field. All independently selected input interactions and
placements are taken through the same finite marked charge. -/
theorem raw (X : ℂ→Ω→Poly Γ) (hG : ∀z,Actual.Good μ (X z)) (s : Γ.Mode)
    (k : ZMod (weight w s+1)) :
    ManuscriptQLocalSourceFourier.project (fun i : ZMod (weight w s+1)=>
      (Actual.charge μ (X (ManuscriptQLocalSourceFourier.phase i))).part s) k =
      ∫u,Fourier.coefficient (fun z u=>(X z u).part s) k u ∂μ :=
  Fourier.measured (D:=weight w s) (μ:=μ) (fun z u=>(X z u).part s)
    (fun i=>hG (ManuscriptQLocalSourceFourier.phase i) s) k

end YM.Integration.ManuscriptQLocalShiftIntegral
end

section
/-! The entire countable native primitive marked source is a finite polynomial
in its independent displacement variable. The signed coefficients are original
row sums on each true occupied mode. No input test, configuration, auxiliary
coupling, or Wick forest is fixed before the source tariff. -/
namespace YM.Integration.ManuscriptQLocalPhaseMark

open Finset Lattice Wilson RG Marker Multi Exterior
open ComparisonDensity.Address RG3.Script.Picnic LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric Comparison.RG02
open ManuscriptQLocalPacketGrades ManuscriptQLocalShiftLedger
open scoped Classical BigOperators

variable {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
  {D : V → ComparisonDensity.Address.Orbit} {G : Gauge} {n : Side}
  (P : MarkedPackets D G n Γ)

def slot (i : ℕ) : Fin (P.powerCap+1) :=
  ⟨min (P.power i).toNat P.powerCap,Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

def cell (g : ℝ) (x : TestSpace D) (t : ℝ) (U : Config G n) (s : Γ.Mode) (i : ℕ) :=
  (Poly.send (P.mode i) (((effective P).packets g).term x t U i)).part s

omit [Fintype V] in
private theorem row (g : ℝ) (x : TestSpace D) (t : ℝ) (U : Config G n) (s : Γ.Mode)
    (z : ℂ) (i : ℕ) :
    (Poly.send ((phaseSource P g z).mode i) ((phaseSource P g z).term x t U i)).part s =
      z^(slot P i).val * cell P g x t U s i := by
  change (Poly.send (P.mode i) ((phaseSource P g z).term x t U i)).part s=_
  rw [Poly.part_send,phase_term]
  unfold cell
  rw [Poly.part_send]
  by_cases he : s=P.mode i
  · simp only [he,if_true]
    cases ht : P.packet i with
    | none => simp [MarkedPackets.term,Grading.packets,Grading.amplified,ht]
    | some T =>
      have hb : (P.power i).toNat ≤ (P.power i).natAbs := by cases P.power i <;> simp
      rw [show (slot P i).val=(P.power i).toNat from min_eq_left (hb.trans (P.power_bounded _ T ht))]
  · simp [he]

omit [Fintype V] in
private theorem quiet (g : ℝ) (x : TestSpace D) (t : ℝ) (U : Config G n) (i : ℕ) :
    cell P g x t U Γ.quiet i=0 := by
  rw [cell,Poly.part_send]
  by_cases h : Γ.quiet=P.mode i
  · rw [if_pos h]
    cases ht : P.packet i with
    | none => simp [MarkedPackets.term,Grading.packets,Grading.amplified,ht]
    | some T => exact ((P.marked i T ht) h.symm).elim
  · exact if_neg h

/-- Countable original rows carrying the same displacement, before connection. -/
def column (g : ℝ) (x : TestSpace D) (t : ℝ) (U : Config G n) (s : Γ.Mode)
    (k : Fin (P.powerCap+1)) : ℂ :=
  ∑'i,if slot P i=k then cell P g x t U s i else 0

def ink (g : ℝ) (x : TestSpace D) (t : ℝ) (U : Config G n) (s : Γ.Mode) : Polynomial ℂ :=
  ∑ k : Fin (P.powerCap+1),Polynomial.C (column P g x t U s k)*Polynomial.X^k.val

omit [Fintype V] in
theorem degree (g : ℝ) (x : TestSpace D) (t : ℝ) (U : Config G n) (s : Γ.Mode) :
    (ink P g x t U s).natDegree≤P.powerCap := by
  apply degree_sum
  intro k _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt_succ k.isLt)

variable {P} {p : BudgetPoint} {address : V→Support n}
  {region : Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
  {w : V→ℝ} {g width budget : ℝ} {offset slope : ℕ}
  (hP : P.Paid p address region w g width budget offset slope) (hg : g≠0)

omit [Fintype V] in
include hP hg in
private theorem collected (x : TestSpace D) (t : ℝ) (U : Config G n) (z : ℂ) (s : Γ.Mode) :
    let f i := (Poly.send ((phaseSource P g z).mode i)
      ((phaseSource P g z).term x t U i)).part s
    Summable f ∧ ∑'i,f i = ∑k : Fin (P.powerCap+1),z^k.val*column P g x t U s k := by
  have hs := NativePaidPacketColors.read_summable ((effective P).paid hg hP) hg x t U
  have hbase : Summable (cell P g x t U s) := Pi.summable.mp hs s
  let f (k : Fin (P.powerCap+1)) (i : ℕ) := if slot P i=k then cell P g x t U s i else 0
  have hc (k) : Summable (f k) := by
    apply (hbase.indicator {i : ℕ | slot P i=k}).congr
    intro i
    simp only [f,Set.indicator_apply,Set.mem_setOf_eq]
  have hz (k : Fin (P.powerCap+1)) := (hc k).mul_left (z^k.val)
  have eqn (i : ℕ) :
      (Poly.send ((phaseSource P g z).mode i) ((phaseSource P g z).term x t U i)).part s =
        ∑k : Fin (P.powerCap+1),z^k.val*f k i := by
    rw [row]
    simp [f,mul_ite,eq_comm (a:=slot P i)]
  refine ⟨(summable_sum (fun k _=>hz k)).congr (fun i=>(eqn i).symm),?_⟩
  rw [tsum_congr eqn,Summable.tsum_finsetSum (fun k _=>hz k)]
  exact sum_congr rfl fun k _=>(hc k).tsum_mul_left (z^k.val)

include hP hg in
theorem measured (x : TestSpace D) (t : ℝ) (U : Config G n) (z : ℂ) (s : Γ.Mode) :
    (ink P g x t U s).eval z = ((phaseSource P g z).read x t U).part s := by
  have hsum : Summable (fun i=>Poly.send ((phaseSource P g z).mode i)
      ((phaseSource P g z).term x t U i)) :=
    Pi.summable.mpr fun j=>(collected hP hg x t U z j).1
  rw [MarkedPackets.read,Poly.share hsum,(collected hP hg x t U z s).2]
  unfold ink
  rw [eval_sum]
  apply sum_congr rfl
  intro k _
  rw [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  exact mul_comm ..

include hP hg in
theorem source (x : TestSpace D) (t : ℝ) (U : Config G n) :
    Ledger (fun _ : V=>P.powerCap) (fun z=>(phaseSource P g z).read x t U) := by
  intro s
  by_cases h : s.val.Nonempty
  · refine ⟨ink P g x t U s,(degree P g x t U s).trans ?_,fun z=>measured hP hg x t U z s⟩
    obtain ⟨v,hv⟩:=h
    exact Finset.single_le_sum (f:=fun _ : V=>P.powerCap) (fun _ _=>Nat.zero_le _) hv
  · have he : s=Γ.quiet := not_not.mp fun hn=>h ((Cumulants.hot_iff_ne s).2 hn)
    subst s
    refine ⟨0,by simp,fun z=>?_⟩
    rw [← measured hP hg x t U z Γ.quiet]
    simp [ink,column,quiet]

include hP hg in
/-- The independent auxiliary phase is preserved by the full marked
finite-field exponential, including every nonempty product mode. -/
theorem ordinary (x : TestSpace D) (t : ℝ) (U : Config G n) :
    Ledger (fun _ : V=>P.powerCap) (fun z=>Poly.pass ((phaseSource P g z).read x t U)) :=
  (source hP hg x t U).pass

end YM.Integration.ManuscriptQLocalPhaseMark
end
