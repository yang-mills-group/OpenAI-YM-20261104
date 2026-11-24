import YM.RG05Readout.Many.Pick
import YM.RG05Readout.Aligned.Geometry

/-! The price at a directly paid higher reporting row needed to unweight the
same ordinary marked course down to its actual origin. The palette Q and
every historical radius loss are retained, with no restriction on the
number of dates. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestIntervalPrice
open Finset Function Lattice Wilson RG Marker RG05Readout.Many
open scoped Classical BigOperators

variable {G : Gauge} (C : Family G)

def bill (n t d k : ℕ) (Q : ℝ) : ℝ :=
  (C.path.levels.clock.hatBeta t)^((3*k+4)*(t-n)+k) * Q * (C.S.a n / C.S.a t)^d

private theorem head {n t d k : ℕ} {Q : ℝ} (nt : n ≤ t) (size : 1 ≤ Q) :
    1 ≤ bill C n t d k Q := by
  have ratio : 1 ≤ C.S.a n / C.S.a t :=
    (one_le_div (C.S.a_pos t)).2 (C.S.strictAnti.antitone nt)
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (C.path.levels.fits.delayed t).le) size) (one_le_pow₀ ratio)

private theorem radius (simple : G.Simple) {n t d k i : ℕ} {Q : ℝ} (ni : n ≤ i) (it : i ≤ t)
    (size : 1 ≤ Q) : 0 < envelope C t d k Q i ∧
    1 ≤ bill C n t d k Q * envelope C t d k Q i := by
  let β:=C.path.levels.clock.hatBeta
  let v:=3*k+4
  have bp (j : ℕ) : 0 < β j := zero_lt_one.trans (C.path.levels.fits.delayed j)
  have positive : 0 < envelope C t d k Q i := mul_pos (rust_paid (C:=C) (m:=t) (k:=k) i).1
    (grantw (totalpos (C:=C) (d:=d) (m:=t) (zero_lt_one.trans_le size) i))
  refine ⟨positive, (inv_le_iff_one_le_mul₀ positive).1 ?_⟩
  have inv : (envelope C t d k Q i)⁻¹ =
      (∏ j ∈ Ico i t,(β j)^v)*(β i)^k*Q*(C.S.a i/C.S.a t)^d := by
    simp [envelope,west,markWidth,total,rusty,not_lt.mpr it,div_eq_mul_inv,mul_inv_rev,
      β,v,mul_assoc,mul_comm,mul_left_comm]
  have rust : (∏ j ∈ Ico i t,(β j)^v) ≤ ((β t)^v)^(t-n) := by
    calc _ ≤ ∏ _j ∈ Ico i t,(β t)^v :=
            prod_le_prod (fun j _=>pow_nonneg (bp j).le _) (fun j hj=>
              pow_le_pow_left₀ (bp j).le (beta_le' (C:=C) simple (mem_Ico.mp hj).2.le) _)
         _ = ((β t)^v)^(t-i) := by simp
         _ ≤ _ := pow_le_pow_right₀ (one_le_pow₀ (C.path.levels.fits.delayed t).le)
            (Nat.sub_le_sub_left ni t)
  have hi : (β i)^k ≤ (β t)^k := pow_le_pow_left₀ (bp i).le (beta_le' (C:=C) simple it) k
  have a0 := div_nonneg (C.S.a_pos i).le (C.S.a_pos t).le
  have extent := pow_le_pow_left₀ a0
    (div_le_div_of_nonneg_right (C.S.strictAnti.antitone ni) (C.S.a_pos t).le) d
  have stocked := mul_le_mul rust hi (pow_nonneg (bp i).le _) (pow_nonneg (pow_nonneg (bp t).le v) _)
  have palette := mul_le_mul_of_nonneg_right stocked (zero_le_one.trans size)
  have total0 := mul_nonneg (mul_nonneg (pow_nonneg (pow_nonneg (bp t).le v) (t-n))
    (pow_nonneg (bp t).le k)) (zero_le_one.trans size)
  rw [inv]
  simpa only [bill,β,v,pow_add,pow_mul] using mul_le_mul palette extent (pow_nonneg a0 _) total0

theorem modes {V : Type} [DecidableEq V] {J : Census V} (simple : G.Simple)
    {n i t d k L : ℕ} {Q : ℝ} (ni : n ≤ i) (it : i ≤ t) (size : 1 ≤ Q)
    (s : J.Mode) (count : s.val.card ≤ L) :
    1 ≤ bill C n t d k Q ^ L * Poly.toll (fun _ : V => envelope C t d k Q i) s := by
  have coin := radius (C:=C) (d:=d) (k:=k) simple ni it size
  have paid : 1 ≤ ∏ _v ∈ s.val, bill C n t d k Q * envelope C t d k Q i :=
    one_le_prod fun _ _ => coin.2
  rw [prod_mul_distrib,prod_const] at paid
  exact paid.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (head C (ni.trans it) size) count)
    (prod_nonneg fun _ _=>coin.1.le))

theorem spend {V : Type} [DecidableEq V] {J : Census V} (simple : G.Simple)
    {n i t d k L : ℕ} {Q δ E : ℝ} (ni : n ≤ i) (it : i ≤ t) (size : 1 ≤ Q)
    (s : J.Mode) (count : s.val.card ≤ L) (positive : 0 ≤ δ)
    (atTop : δ * bill C n t d k Q^L ≤ E) :
    δ ≤ E*Poly.toll (fun _ : V => envelope C t d k Q i) s := by
  have paid := modes C simple ni it size s count (d:=d) (k:=k)
  calc δ = δ*1 := (mul_one _).symm
       _ ≤ δ*(bill C n t d k Q^L*Poly.toll (fun _ : V => envelope C t d k Q i) s) :=
         mul_le_mul_of_nonneg_left paid positive
       _ ≤ _ := by
         rw [← mul_assoc]
         exact mul_le_mul_of_nonneg_right atTop (Poly.worth (fun _=>(radius C simple ni it size).1) _).le

end YM.Integration.WilsonAllDateHarvestIntervalPrice

