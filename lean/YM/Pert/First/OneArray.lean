import YM.Pert.First.ActionVertex
/-! Exact first bare position amplitude = one cubic vertex plus a sum of individual varied marks. (On the joint diagrams numerator vs denominator, not dropping vacuum factors per mark.) -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Pert.First
open PowerSeries MeasureTheory Orb Full Function Lattice Filter Labels
open scoped Topology Classical
variable {G : Gauge} {N : Side}
lemma unit_inv : constantCoeff (vacuum G N)⁻¹ = 1 := by rw [constantCoeff_inv,show constantCoeff (vacuum G N)= 1 by simpa only [coeff_zero_eq_constantCoeff_apply] using (vacuum_flat (G:=G) (n:=N)),inv_one]
lemma normalize_one (f : JetArray (Coords G N)) :
    PowerSeries.coeff 1 (Orb.normalize f) = ∫ x, PowerSeries.coeff 1 (weight G N x) * constantCoeff (f x)+PowerSeries.coeff 1 (f x) ∂data G N := by
  unfold Orb.normalize expect; rw [coeff_one_mul, coeff_mk, unit_inv,vacuum_inv_one,mul_one,zero_mul,add_zero]; congr 1; funext x
  rw [Pi.mul_apply,coeff_one_mul,← coeff_zero_eq_constantCoeff,weight_flat,mul_one]
lemma cubic_tame : Tame (cubic (G:=G) (N:=N)) := by
  unfold cubic
  rw [show (fun x : Coords G N=> -(↑(scaleJet (action G N) 3 x):ℂ)) = (-1:ℝ) • (fun x : Coords G N=> (↑(scaleJet (action G N) 3 x):ℂ)) from funext (fun x=> by simp [Complex.real_smul])]
  simpa only [Pi.smul_apply, Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_one,neg_mul,one_mul, ←Complex.ofReal_neg] using (Orb.tame_scaleJet (action G N) 3).ofReal.scalar_const (-1:ℝ)
variable {R B : Type*} [CommSemiring R] [DecidableEq B]
/-- Product rule in the formal diagram algebra. -/
def lead := PowerSeries.constantCoeff (R:=R)
def first := PowerSeries.coeff (R:=R) 1
lemma first_product (f : B → PowerSeries R) (s : Finset B) :
    first (∏ i∈s,f i) = ∑ i∈s, (first (f i) * ∏ j∈s.erase i, lead (f j)) := by
  induction s using Finset.induction_on with
  | empty=> simp [first]
  | insert a s hs ih=>
     rw [Finset.prod_insert hs]; unfold first; rw [coeff_one_mul]; change first (f a)*lead _ + first (∏i∈s,f i)*lead _=_ -- remove last
     rw [Finset.sum_insert hs, Finset.erase_insert, ih,lead,map_prod]; congr 1
     rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i hi=>?_
     have hne : i ≠ a := ne_of_mem_of_not_mem hi hs
     rw [Finset.erase_insert_of_ne (Ne.symm hne), Finset.prod_insert (fun h=>hs (Finset.mem_of_mem_erase h)), first]; ring
     exact hs

variable {I : Type} [DecidableEq I] (s : Finset I) (o : I→Site N) (h : ℝ) (cap : I→ℕ) (p : I→Pol G)
def tube (x i) := lead (column (cap i) h (o i) (p i) x)
def dry (x i) := first (column (cap i) h (o i) (p i) x)
def line (x) := ∏ i∈s, tube o h cap p x i
def varied (x i) := dry o h cap p x i * line (s.erase i) o h cap p x
lemma product_exact (x : Coords G N) : product cap h s o p x = ∏ i∈s,column (cap i) h (o i) (p i) x := by simp [product,Finset.prod_apply]
lemma tube_tame (i) : Tame (fun x=>tube o h cap p x i) := by simpa only [tube,lead,coeff_zero_eq_constantCoeff_apply] using (column_ready h (o i) (p i) 0 (d:=cap i))
lemma dry_tame (i) : Tame (fun x => dry o h cap p x i) := column_ready _ _ _ 1
lemma line_tame : Tame (line s o h cap p) := by
  unfold line; rw [show (fun x=> (∏i∈s,tube o h cap p x i))=(∏i∈s,(fun x=>tube o h cap p x i)) by ext1; simp only [Finset.prod_apply]]
  induction s using Finset.induction_on with
  | empty=> rw [Finset.prod_empty]; exact Tame.constant _
  | insert a s hs ih => rw [Finset.prod_insert hs]; exact (tube_tame o h cap p a).mul ih
lemma varied_tame (i) : Tame (fun x=>varied s o h cap p x i) := Tame.mul (dry_tame o h cap p i) (line_tame _ o h cap p)
def exposed :=
   (∫ x, cubic x * line s o h cap p x ∂data G N) + ∑ i∈s, ∫ x, varied s o h cap p x i ∂data G N
lemma first_amplitude (hg : G.Simple) : first (amplitude cap h s o p) = exposed s o h cap p := by
  unfold first amplitude; rw [normalize_one]; simp_rw [has_first hg,product_exact, map_prod]; unfold exposed; rw [← integral_finsetSum, ← integral_add]
  · congr 1; funext x; congr 1; exact first_product ..
  · exact (Tame.mul cubic_tame (line_tame ..)).integrable
  · exact integrable_finsetSum s (fun i _=> (varied_tame s o h cap p i).integrable) -- note order
  · exact fun i _ => (varied_tame s o h cap p i).integrable
end YM.Pert.First
