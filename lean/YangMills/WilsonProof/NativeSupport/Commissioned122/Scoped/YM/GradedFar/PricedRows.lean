import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Prices
import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Crop

/-!
# Formal arrays on whole Appointed122Fields, tariff and charges after the field grade payment
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Filter Function Set Scale O O.Enh O.Score O.Project O.Read O.Canon PowerSeries
open Dframe XSpace XSpace.Normalize
open scoped Classical BigOperators Topology

variable {G : Gauge} {n m h k p H : ℕ} (V : Arenas G)
    {d : Fin n → ℕ} {e : Fin m → ℕ}

/-- Extend the prescribed output coefficients by multilinearity in all Near inputs,
on the same Q alphabet as in Main.Match.separatedOPE. -/
def tariff (x : Points n) (u : Appointed122Fields G d) (q : Q G) : PowerSeries ℂ :=
  ∑ i : Words G d, C (filedMultipliers122 u i) * FarCoefficients V (labeling i) x q

/-- Explicitly recover the literal graded entries of the output. -/
lemma tariff_on_label (x : Points n) (u : Words G d) (q : Q G) :
    tariff V x (basisFields u) q = FarCoefficients V (labeling u) x q := by
  unfold tariff; rw [Finset.sum_eq_single u]
  · rw [multiplier_basis, if_pos rfl, map_one, one_mul]
  · intro i _ h; rw [multiplier_basis, if_neg (Ne.symm h), map_zero, zero_mul]
  · simp

/-- The *evaluated* formal coefficient vector c of (M.1) in the actual space through h. -/
def filedVector122 (x : Points n) (h p : ℕ) (z : ℂ) (u : Appointed122Fields G d) : Sec G h :=
  ∑ i : Toon G h, filedCrop122 p z (tariff V x u (flash i)) • theory i

lemma vector_entry (x : Points n) (h p : ℕ) (z : ℂ) (u : Appointed122Fields G d) (q : Toon G h) :
    coord q (filedVector122 V x h p z u) = filedCrop122 p z (tariff V x u (flash q)) := by
  unfold filedVector122; rw [map_sum]; simp_rw [_root_.map_smul, pivotδ]; simp

variable (B : ℝ → Frames G)
/-- Residual power series (before *any* crops). -/
def residual (t : ℝ) (x : Points n) (y : Points m) (h : ℕ) (hd : Covered d H)
    (he : Covered e H) (lh : h ≤ H) (u : Appointed122Fields G d) (v : Appointed122Fields G e) : PowerSeries ℂ :=
  series V B (-t) (forest x (squeeze (-t) y)) hd he u v - ∑ i : Toon G h,
    tariff V x u (flash i) * rowsResponse122 V B (-t) (outgoing (squeeze (-t) y)) h lh he v (theory i)

-- preserve signed subtraction in the assembly from that graded proof.
lemma near_residual (t : ℝ) (x : Points n) (y : Points m) (hd : Covered d H)
    (he : Covered e H) (lh : h ≤ H) (u : Appointed122Fields G d) (v : Appointed122Fields G e) :
    residual V B t x y h hd he lh u v = ∑ i : Words G d,
      C (filedMultipliers122 u i) * residual V B t x y h hd he lh (basisFields i) v := by
  unfold residual; simp_rw [tariff_on_label, mul_sub, Finset.mul_sum, ← mul_assoc]
  rw [decompose_near _ _ _ _ _ _ u, Finset.sum_sub_distrib, Finset.sum_comm (s:=Finset.univ (α:=Words G d))]
  simp_rw [tariff, Finset.sum_mul]

lemma far_residual (t : ℝ) (x : Points n) (y : Points m) (hd : Covered d H)
    (he : Covered e H) (lh : h ≤ H) (u : Appointed122Fields G d) (v : Appointed122Fields G e) :
    residual V B t x y h hd he lh u v = ∑ i : Words G e,
      C (filedMultipliers122 v i) * residual V B t x y h hd he lh u (basisFields i) := by
  unfold residual rowsResponse122; simp_rw [mul_sub, Finset.mul_sum,
    mul_left_comm (C (filedMultipliers122 v _)) (tariff V x u _) ]
  simp_rw [decompose_far _ _ _ _ _ _ _ v, Finset.mul_sum]; rw [Finset.sum_sub_distrib]
  congr 1; exact Finset.sum_comm

lemma residual_show (t : ℝ) (x : Points n) (y : Points m) (hd : Covered d H)
    (he : Covered e H) (lh : h ≤ H) (u : Words G d) (v : Words G e)
    {ψ : ℝ → PowerSeries ℂ} (law : Law V ψ B) (regular : Regular V) :
    residual V B t x y h hd he lh (basisFields u) (basisFields v) =
      looseT B (install V) t (labeling u) (labeling v) (FarCoefficients V (labeling u)) h x y := by
  unfold residual looseT; simp_rw [expand_show law hd he regular,
    expand_long law he regular lh, tariff_on_label]

variable {V B}
    {ψ : ℝ → PowerSeries ℂ} (phys : Canon.Physical V ψ B)
    (law : Law V ψ B)

lemma budget_charge {I : Type} (u : I → Appointed122Fields G d) {R : ℝ} (within : ∀ i, FieldBudget (u i) R)
    (p : ℕ) (P : Words G d) : ChargeP (p+1) 0 (fun (i:I) (_:ℝ) => C (filedMultipliers122 (u i) P)) :=
  ChargeP.constants (Rain.cash ⟨_, fun i => multiplier_budget (u i) (within i) P⟩)

variable {K : Set (Points n)} {S : Set (Points m)}
    (kc : IsCompact K) (hk : K ⊆ conf n) (sc : IsCompact S) (hs : S ⊆ Outside m)
    -- the joint family; can include any extra viewer/phase parameters, with
    -- the very same formal Sec inputs in all comparisons.
    {I : Type} (x : I → Points n) (hx : ∀ i, x i ∈ K) (y : I → Points m) (hy : ∀ i, y i ∈ S)
    (hd : Covered d H) (he : Covered e H)
    (u : I → Appointed122Fields G d) (v : I → Appointed122Fields G e) {R L : ℝ}
    (within : ∀ i, FieldBudget (u i) R) (along : ∀ i, FieldBudget (v i) L)
include phys kc hk sc hs hx hy within along law

lemma residual_charge (h p : ℕ) (lh : h ≤ H) : ChargeP (p+1) ((h:ℝ)+1)
    (fun (i : I) t => residual V B t (x i) (y i) h hd he lh (u i) (v i)) := by
  let f (i : I) : ↥K × ↥S := (⟨x i,hx i⟩, ⟨y i,hy i⟩)
  have h₁ i t := near_residual V B t (x i) (y i) hd he lh (u i) (v i)
  have h₂ (P : Words G d) i t := far_residual V B t (x i) (y i) hd he lh (basisFields P) (v i)
  simp_rw [h₁, h₂]
  apply ChargeP.sum; intro P _; refine ChargeP.times (budget_charge u within p P) ?_
  apply ChargeP.sum; intro W _; refine ChargeP.times (budget_charge v along p W) ?_
  simp_rw [residual_show V B _ _ _ hd he lh P W law phys.dimensions]; exact
    (loose_price phys kc hk sc hs (labeling P) (labeling W) law h p).pull f

lemma full_charge (h p : ℕ) : ChargeP (p+1) 0 (fun (i : I) t =>
    series V B (-t) (forest (x i) (squeeze (-t) (y i))) hd he (u i) (v i)) := by
  let z i (t : ℝ) := forest (x i) (squeeze (-t) (y i))
  have h₁ i t := decompose_near V B (-t) (z i t) hd he (u i) (v i)
  have h₂ (P : Words G d) i t := decompose_far V B (-t) (z i t) hd he (basisFields P) (v i)
  unfold z at h₁ h₂; simp_rw [h₁, h₂]
  apply ChargeP.sum; intro P _; refine ChargeP.times (budget_charge u within p P) ?_
  apply ChargeP.sum; intro W _; refine ChargeP.times (budget_charge v along p W) ?_
  simp_rw [expand_show law hd he phys.dimensions]
  exact (show_price phys kc hk sc hs (labeling P) (labeling W) law h p).pull
    (fun i => (⟨x i,hx i⟩, ⟨y i,hy i⟩))

omit kc hk hx within in
lemma response_charge (p : ℕ) (lh : h ≤ H) (q : Toon G h) : ChargeP (p+1) (heft (flash q) : ℝ)
    (fun (i : I) t => rowsResponse122 V B (-t) (outgoing (squeeze (-t) (y i))) h lh he (v i) (theory q)) := by
  have hP i (t : ℝ) : rowsResponse122 V B (-t) (outgoing (squeeze (-t) (y i))) h lh he (v i) (theory q) =
    ∑ P : Words G e, C (filedMultipliers122 (v i) P) * rowsResponse122 V B (-t) (outgoing (squeeze (-t) (y i))) h lh he (basisFields P) (theory q) := decompose_far ..
  simp_rw [hP, expand_long law he phys.dimensions lh]; apply ChargeP.sum; intro W _
  exact ChargeP.times (budget_charge v along p W)
    ((long_price phys sc hs (labeling W) (flash q) law p).pull (fun i => ⟨y i,hy i⟩))

omit sc hs hy along law in
lemma fare_charge (p : ℕ) (q : Q G) : ChargeP (p+1) 0
    (fun (i:I) _ => tariff V (x i) (u i) q) := by
  unfold tariff; apply ChargeP.sum; intro P _
  exact ChargeP.times (budget_charge u within p P)
    ((tariff_charge phys kc hk (labeling P) q p).pull (fun i => ⟨x i,hx i⟩))

/- Though log powers would suffice in the final excess-degree estimate, the actual
tariff on inner coefficients is bounded (independent of log T). -/
omit sc hs hy along law in
lemma bounded_tariff (q : Q G) (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ i : I, ‖coeff k (tariff V (x i) (u i) q)‖ ≤ C := by
  -- Even our proof via `fare_charge` already implies that absolute fee, due
  -- to how its quantifiers enter (t chosen *first*, i not varying the price).
  obtain ⟨C,hC,a,j⟩ := fare_charge phys kc hk x hx u within k q k (Nat.lt_succ_self _)
  obtain ⟨t, ht, hp⟩ := (j.and (eventually_ge_atTop (0:ℝ))).exists
  exact ⟨C*post 0 t a, mul_pos hC (post_at hp), ht⟩
end YM.FVA2.GradedFar
