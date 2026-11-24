import YM.Comparison.Density.Payload.Registers
import YM.Push.ABSOLUTE_SUMS.Footprint
/-!
# Marker incidence without a volume cost. Pay known spatial reception
of marks and exponent reserve before turning any roots budget into a
per-site hit estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Budgets
open Testing Markers Registers Marker RG Lattice Function MeasureTheory Filter Wilson
open Pert.Attach Push.AbsoluteSums Finset Lattice.Corona
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {ι : Type*} {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
variable {G : Gauge} {n : Side} {X : V → Type} {O : Origin V n}

-- Projected roots multiplicity after a push may include a factor
-- for preimage volume and also number of complete placements.
def Admissions (O : Origin V n) (N : ℕ) := ∀ x : Site n, (univ.filter (fun v:V => O.root v=x)).card ≤ N

def dues (B : BudgetPoint) (N : ℕ) (c e : ℝ) := Footprint.payment 1 (4*B.B+2) 0 1 1 (N*c) (B.supportExponent+e) 0

-- shared by canon and mirror attachment. Assigned to pivotal
-- *marker*, not weight-degree. Cases with zero weights may lack a
-- footprint; still check part and noncontribution.
theorem budget_marks (B : BudgetPoint) (F : ι → Support n) (f : ι→ℝ) (hf : ∀ i,0 ≤ f i) (L : ι → V)
    (hF : ∀ i,f i≠0 → O.root (L i)∈F i) (N : ℕ) (hp : Admissions O N)
    {c e : ℝ} (hc : 0 ≤ c) (he : 0≤ e)
    (h : ∀ v, SumBudget (fun i => if L i=v then (later B (e+2) (by linarith)).mass (F i) (f i) else 0) c) :
    Ac.Hit F B.B f (B.supportExponent+e) (dues B N c e) := by
  let x:= fun i=> O.root (L i)
  let Z (i) := if f i=0 then ∅ else F i
  let Y:=fun i=> coverNumber B.B (F i)
  let P := later B (e+2) (show 0≤e+2 by linarith)
  have hh : Footprint.Anchored x f Y P.supportExponent (N*c) := by
    intro v; let U:= univ.filter (fun u=> O.root u=v)
    let D (j:V) i := if L i=j then P.mass (F i) (f i) else 0
    have ht := budget_over U D (fun _=>c) (fun j _=> h j)
    have hz : SumBudget (fun i=> ∑ j∈U,D j i) (N*c):=budget_loosen ht (by
      simp only [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hp v) hc)
    convert hz using 2 with i
    unfold D x; simp only [sum_ite_eq,U,mem_filter,mem_univ,true_and]
    split_ifs; exact mul_comm ..; rfl
  have hW (i : ι) (s : Site n) (hh:s∈Z i): separation s (x i) ≤ (4*B.B+2)*(1+Y i):= by
    by_cases h:f i=0
    · simp [Z,h] at hh
    have he:= extent (F i) B.B (show s∈F i from by simpa [Z,h] using hh) (hF _ h)
    refine he.trans ?_; unfold Y; nlinarith
  have hy (i : ι) : (coverNumber B.B (Z i):ℝ) ≤ 0+1*(Y i):= by
    simp only [one_mul,zero_add]
    exact_mod_cast cover_mono (show Z i⊆F i from by unfold Z; split; simp; rfl) B.B
  have hP: Footprint.reserve P.supportExponent (B.supportExponent+e) 1 1:= by
    refine ⟨add_nonneg B.exponent_pos.le he, zero_lt_one,?_⟩; unfold P later; dsimp; linarith
  have hk := Footprint.assigned id 1 (fun s : Support n=> by simp) x f hf Y Z hh _ 0 _ hW hy (C:=1) zero_le_one hP f hf (fun i=> by simp)
  intro i; unfold dues; convert hk i using 2 with j; by_cases hs:f j=0
  · by_cases hZ:i∈F j <;> simp only [Z,if_pos hs,hs,zero_mul,ite_self]
  simp only [Z,if_neg hs]

lemma freight_pays {B : BudgetPoint} {Y : Address R→ Support n} {w : V → ℝ} {e b : ℝ}
    (hw : ∀ i,0<w i) (he : 0≤e) {a : Address R → ℝ} (h : Freight (later B (e+2) (by linarith)) w Y a b)
    (hY : ∀ i,a i≠0 → ∀ v∈i.1.sites,O.root v∈Y i) {N : ℕ} (hp : Admissions O N) :
    Ac.Hit Y B.B (fun i=> Poly.toll w i.1.val * a i) (B.supportExponent+e) (dues B N b e) := by
  choose l hl using fun i : Multi.Hot R=> i.property
  let g (i : Address R):= Poly.toll w i.1.val * a i
  have heG i : 0≤g i:= mul_nonneg (Poly.worth hw _).le (h.2.1 _)
  apply budget_marks B _ g heG (fun i=> l i.1) (fun i hu=> hY i (fun ht=>hu (by simp [g,ht])) _ (hl _)) N hp h.1 he
  intro i
  refine budget_mono (h.2.2 i) (fun j=> ?_) (fun j=> ?_)
  · split; exact mul_nonneg (Real.exp_pos _).le (heG _); exact le_rfl
  split_ifs with hL hT
  · unfold BudgetPoint.mass g; rw [mul_left_comm]
  · exact False.elim (hT (hL ▸ hl _))
  · exact mul_nonneg (Poly.worth hw _).le (mul_nonneg (Real.exp_pos _).le (h.2.1 _))
  exact le_rfl
end YM.Comparison.Density.Budgets
