import YangMills.WilsonProof.NativeSupport.Commissioned259.ScaleCost.Exhibit
/-! # Simultaneous eigen-budget (no eigenvectors) in the physical frame calculation G.2

Need the exact filtration at actual fields; this is what sets the scale of the
physical-basis column. Assume compatibility with inclusions (Leading theorem on physical
frames; use jointly to any fixed finite horizon at an anchor). Then polymer currency for all
columns and all inverse components. No determinant lower bound *assumed* over varying scales.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.ScaleCost
open Filter Set Function Asymptotics MeasureTheory PowerSeries Matrix
open MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land Register FVA2.Scale
open XSpace XSpace.Normalize O.Score O.Enh Dframe Comparing
open scoped Topology Classical BigOperators Matrix
local notation "late" => 𝓝[>] (0:ℝ)
variable {G : Gauge} {V : Arenas G} {R : ℝ→PowerSeries ℂ}
    {B : ℝ→Frames G} {D : Route G} {d : ℕ} (hG : G.Simple)
-- turn Income into a polylog tariff for any normed measurements.
-- profit-bank at cash; Pricing MUST NOT accrue any powers of T (especially when Far readings
-- at log-stretch g⁻¹). Turn into the single-length norm estimate via holdings.
def Capital {E : Type*} [Norm E] (f : ℝ→E) := ∃ k:ℕ, f =O[late] (fun i=>cash i^k)
namespace Capital
variable {I E : Type*} [NormedAddCommGroup E] {f u g : ℝ→E}
lemma stands (f : ℝ→E) : Capital f ↔ Income (fun i=> ‖f i‖) := by
  simp_rw [Capital,Income,isBigO_norm_left]
include hG in
lemma earns (h : Capital f) : ∃ k:ℕ, f =O[late] fun i=> (g0 G i)⁻¹ ^ k := by
  obtain ⟨k,H⟩:= payload hG ((stands f).mp h); exact ⟨k,isBigO_norm_left.mp H⟩
lemma pays (f : E) : Capital (fun (_:ℝ)=>f) := ⟨0,by simpa [pow_zero] using isBigO_const_const (c:=f) (show (1:ℝ) ≠ 0 from one_ne_zero) late⟩
lemma dominated (h : Capital f) {E' : Type*} [NormedAddCommGroup E'] {u : ℝ→E'} (hu : u=O[late] f) : Capital u := by obtain ⟨k,H⟩:= h; exact ⟨k,hu.trans H⟩
lemma accrue (n m : ℕ) (h : n ≤ m) : (fun i=>cash i^n)=O[late] fun i=>cash i^m := by
  refine IsBigO.of_bound' ?_; filter_upwards [holds_cash.eventually_ge_atTop 1] with i hi; rw [norm_pow,norm_pow]; exact pow_le_pow_right₀ (hi.trans (le_abs_self _)) h
lemma add (h : Capital f) (u : Capital g) : Capital (fun i=> f i+g i) := by
  obtain ⟨k,H⟩:= h; obtain ⟨l,L⟩:= u; exact ⟨max k l,(H.trans (accrue k _ (le_max_left ..))).add (L.trans (accrue l _ (le_max_right ..)))⟩
lemma mul {E : Type*} [NormedRing E] {f u:ℝ→E} (h : Capital f) (v : Capital u) : Capital (fun i=> f i*u i) := by
  obtain ⟨k,H⟩:= h; obtain ⟨l,L⟩:= v; exact ⟨k+l,(H.mul L).congr_right (fun i=>(pow_add ..).symm)⟩
lemma sum {s : Finset I} {f : I→ℝ→E} (h : ∀ i∈s, Capital (f i)) : Capital (fun i=>∑ j∈s,f j i) := by
  induction s using Finset.induction_on with
  | empty => simp_rw [Finset.sum_empty]; exact pays _
  | insert j s hj ih => simp_rw [Finset.sum_insert hj]; exact (h _ (Finset.mem_insert_self ..)).add (ih fun i hi=> h _ (Finset.mem_insert_of_mem hi))
lemma prod {s:Finset I} {f:I→ℝ→ℂ} (h:∀ i∈s, Capital (f i)) : Capital (fun i=>∏ j∈s,f j i) := by
  induction s using Finset.induction_on with
  | empty => simp_rw [Finset.prod_empty]; exact pays _
  | insert j s hj ih => simp_rw [Finset.prod_insert hj]; exact (h _ (Finset.mem_insert_self ..)).mul (ih fun i hi=> h _ (Finset.mem_insert_of_mem hi))
lemma adjoint (F:ℝ→Operator G d) (i j : Toon G d) (h:∀ i j,Capital (fun r=> F r i j)) : Capital (fun r=> (F r).adjugate i j) := by
  simp_rw [adjugate_apply, Matrix.det_apply']; refine Capital.sum fun σ _=> Capital.mul (pays _) (Capital.prod fun v _=>?_)
  by_cases this : σ v=j
  · simp_rw [this,updateRow_self]; exact pays _
  simp_rw [Matrix.updateRow_ne this]; exact h ..
lemma matrix (F:ℝ→Operator G d) : (Income (stiffness ∘ F)) ↔ ∀ i j, Capital (fun r=>F r i j) := by
  constructor
  · rintro ⟨k,h⟩; exact fun i j=>⟨k,matrixPay.mp h i j⟩
  intro h; exact Capital.sum (fun i (_:i∈(Finset.univ:Finset (Toon G d))) => Capital.sum (fun j (_:j∈(Finset.univ:Finset (Toon G d))) => (stands _).mp (h i j)))
end Capital

-- translate basis using the genuine Walk relation at exact H frames (here numerical).
-- take the anchor from a sufficiently small fixed positive length r_f for cap d.
def mounts (D : Route G) (s : ℝ) (d : ℕ) :=
    ∀ (e : ℕ) (h : e ≤ d), ∀ᶠ r in late, ∀ v: Sec G e, D r s d (up h v) = up h (D r s e v)

include hG
variable (hD : Balances D) (h : Law V R B) (t : ℝ→ℝ) (hz : ∀ d s, coeff 1 (B s d)=0) (field : ∀ d, FieldQuote G B t D d 1)
include hD h t hz field
lemma real_columns (f : ℝ) (hf : mounts D f d) : Income (fun i=>stiffness (value D d f i)) := by
  refine (Capital.matrix _).mpr fun b c=>?_
  let k:=heft (flash c); let E : k ≤ d := size_le c; let u := theory (grab (flash c))
  let L (r:ℝ):= D r f k u; let v (r:ℝ):= numbers (L r); let A r:= value D d f r
  have hp := safe hG v h t (hz k) (field k) (Eventually.of_forall fun r T _ _=> ((Comparing.issued _ _).trans (congr_arg numbers (by unfold L; rw [hD r (r*T) f k]; rfl))).symm)
  have hh (l:Toon G k): Capital (fun r=> (r:ℂ)^k * coord l (L r)) := by
    refine Capital.dominated (show Capital (fun r=>r^k*tallyZ (v r)) from hp) (IsBigO.of_bound' ?_)
    filter_upwards [show ∀ᶠ r in late,0<r from self_mem_nhdsWithin] with r hr
    rw [norm_mul,norm_mul,norm_pow,norm_pow,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ tallyZ (v r) from Finset.sum_nonneg fun i _=>norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun b (_:b∈(Finset.univ:Finset (Toon G k)))=>norm_nonneg (v r b)) (Finset.mem_univ l)) (by positivity)
  have he : ∀ᶠ r in late, A r b c = ∑ l:Toon G k,(r:ℂ)^k * coord l (L r) * coord b (up E (theory l)) := by
    filter_upwards [hf k E, show ∀ᶠ r in late,0<r from self_mem_nhdsWithin] with r hi p
    unfold A value engine; rw [composition',columns,LinearMap.comp_apply,Level.exact₀, Extent.token,neg_neg,Real.exp_log p,_root_.map_smul,_root_.map_smul,smul_eq_mul]
    change (r:ℂ)^k*coord b (D r f d (up E u))=_
    rw [hi]
    change _*coord b (up E (L r))=_; nth_rw 1 [← all_sig (L r)]; simp_rw [map_sum,_root_.map_smul,Finset.mul_sum,smul_eq_mul, ← mul_assoc]; rfl
  refine Capital.dominated (f:=fun r=> ∑ l:Toon G k,(r:ℂ)^k * coord l (L r) * coord b (up E (theory l))) ?_ (IsBigO.of_bound' (he.mono fun r h=>(congr_arg norm h).le))
  exact Capital.sum fun l (_:l∈(Finset.univ:Finset (Toon G k)))=> Capital.mul (hh l) (Capital.pays _)
lemma physical_basis (f : ℝ) (hf : mounts D f d) : Income (fun i=>stiffness (value D d f i)) ∧ Income (fun i=>stiffness (value D d f i)⁻¹) := by
  have hu := real_columns hG hD h t hz field f hf; refine ⟨hu,(Capital.matrix _).mpr fun i j=>?_ ⟩
  let A r:= value D d f r
  change Capital (fun r=>(A r)⁻¹ i j)
  simp_rw [Matrix.inv_def,Ring.inverse_eq_inv',Matrix.smul_apply,smul_eq_mul]
  exact Capital.mul ((Capital.stands _).mpr (determinant hG f hD h t (hz d) (field d))) (Capital.adjoint _ i j ((Capital.matrix _).mp hu))
end YM.FVA2.GradedFar259.ScaleCost
