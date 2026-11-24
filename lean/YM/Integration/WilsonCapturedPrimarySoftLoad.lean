import YM.Integration.WilsonCapturedPrimarySoftInventory
import YM.Integration.WilsonCenteredLampCapture

/-! The source fee depends on occupied load. Unused names and their ambient
period do not enter even the count of signed partitions. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimarySoftLoad
open Function Finset RG Lattice Wilson Marker Multi QuadraticLocal Ac Push.Local Corona
open WilsonCapturedPrimarySoftPartition WilsonCapturedPrimarySoftInventory WilsonCenteredLampCapture
open scoped Classical BigOperators
variable {n : Side} {V : Type} [DecidableEq V] {R : Census V}

theorem subs {s : R.Mode} {q : (parts R).Mode} (admitted : q∈shards R s)
    (t : Hot R) (chosen : t∈q.val) : t.sites⊆s.val := by
  rw [←(mem_filter.mp admitted).2]
  exact fun v hv=>mem_biUnion.mpr ⟨t,chosen,hv⟩

theorem size {s : R.Mode} {q : (parts R).Mode} (admitted : q∈shards R s) :
    q.val.card ≤ s.val.card := by
  rw [←(mem_filter.mp admitted).2]
  change q.val.card≤(q.val.biUnion Hot.sites).card
  rw [card_biUnion (parts_wise q)]
  calc q.val.card = ∑ _∈q.val,1 := by simp
       _ ≤ _ := sum_le_sum fun t _=>card_pos.mpr t.property

theorem count (s : R.Mode) : (shards R s).card ≤ 2^(2^s.val.card) := by
  let bag (q : (parts R).Mode) := q.val.image Hot.sites
  let file (q : ↥(shards R s)) : ↥s.val.powerset.powerset := ⟨bag q.val,by
    apply mem_powerset.mpr
    rintro u hu
    obtain ⟨t,ht,rfl⟩:=mem_image.mp hu
    exact mem_powerset.mpr (subs q.property t ht)⟩
  have faithful : Injective (Hot.sites (R:=R)) := fun _ _ h=>Subtype.ext (Subtype.ext h)
  have unique : Injective file := by
    intro a b equal
    apply Subtype.ext
    apply Subtype.ext
    exact image_injective faithful (congrArg Subtype.val equal)
  simpa only [Fintype.card_coe,card_powerset] using Fintype.card_le_of_injective file unique

def principal (p : BudgetPoint) (Z : Support n) (W C : ℝ) (k : ℕ) :=
  Real.exp ((p.supportExponent+2)*coverNumber p.B Z)*(max 1 (W*C))^k

theorem row (p : BudgetPoint) (Z : Support n) (s : R.Mode) (w : V→ℝ) (hw : ∀v,0<w v)
    {C W : ℝ} (income : 0≤C) (q : (parts R).Mode) (admitted : q∈shards R s)
    {k : ℕ} (fixed : s.val.card≤k) (sold : ∀ t:R.Mode,t.val⊆s.val → (Poly.toll w t)⁻¹≤W) :
    tariff p Z w C q ≤ principal p Z W C k := by
  let M:=max 1 (W*C)
  have each (j : Fin q.val.card) : (Poly.toll w (block q j))⁻¹*C≤M :=
    (mul_le_mul_of_nonneg_right
      (sold _ (subs admitted ((index q) j).val ((index q) j).property)) income).trans (le_max_right _ _)
  have positive (j : Fin q.val.card) : 0< Poly.toll w (block q j) := prod_pos (fun a _=>hw a)
  have pose (j : Fin q.val.card) := mul_nonneg (inv_nonneg.mpr (positive j).le) income
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  calc ∏ j,(Poly.toll w (block q j))⁻¹*C ≤ ∏ _ : Fin q.val.card,M := prod_le_prod (fun j _=>pose j) (fun j _=>each j)
       _ = M^q.val.card := by simp
       _ ≤ M^k := pow_le_pow_right₀ (le_max_left _ _) ((size admitted).trans fixed)

theorem fee (p : BudgetPoint) (Z : Support n) (s : R.Mode) (w : V→ℝ) (hw : ∀v,0<w v)
    {C W : ℝ} (income : 0≤C) {k : ℕ} (fixed : s.val.card≤k)
    (sold : ∀ t:R.Mode,t.val⊆s.val → (Poly.toll w t)⁻¹≤W) :
    fare p Z w C s ≤ ((2^(2^k):ℕ):ℝ)*principal p Z W C k := by
  have many : (shards R s).card≤2^(2^k) := (count s).trans (Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) fixed))
  have positive : 0≤principal p Z W C k := by
    apply mul_nonneg (Real.exp_pos _).le
    exact pow_nonneg (zero_le_one.trans (le_max_left ..)) _
  calc fare p Z w C s ≤ ∑ _∈shards R s,principal p Z W C k :=
         sum_le_sum fun q t=>row p Z s w hw income q t fixed sold
       _ = (((shards R s).card:ℕ):ℝ)*principal p Z W C k := by rw [sum_const,nsmul_eq_mul]
       _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast many) positive

end YM.Integration.WilsonCapturedPrimarySoftLoad
