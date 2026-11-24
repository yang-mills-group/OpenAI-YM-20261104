import YM.Integration.WilsonCapturedPrimarySoftLoad
import YM.Integration.WilsonCapturedPrimarySoftMount

/-! Fixed-load fare of the entire native pure regular field, including each
original mask rebate. The exponent at a given capture is set before accuracy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimarySoftFare
open Function Finset RG Lattice Wilson Marker Multi QuadraticLocal Ac Push.Local Source Labels
open WilsonCenteredLampCapture WilsonCenteredFiledAtoms WilsonCapturedPrimarySoftPartition
open WilsonCapturedPrimarySoftLoad
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] {R : Census V}
    {d : ℕ} {F : Frame G d}

def motion (p : BudgetPoint) (rad k : ℕ) := (((k+1:ℕ):ℝ)*(1+(rad:ℝ))^p.power)^p.order

theorem width (p : BudgetPoint) (rad k : ℕ) (s : R.Mode) (fixed : s.val.card≤k)
    (q : (parts R).Mode) (admitted : q∈shards R s) :
    stage p rad (univ : Finset (Fin q.val.card))≤ motion p rad k := by
  unfold stage motion
  rw [card_univ,Fintype.card_fin]
  have next := Nat.succ_le_succ ((size admitted).trans fixed)
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast next) (by positivity)

def factorFee (p : BudgetPoint) (S : SectionData F) (Y : Hol G) (μ v κ : ℝ) :=
  let D := Push.Local.factor Y S p.supportExponent μ
  let H := hitWidth p*v/κ
  max 0 (D+H+H*D)

theorem original (p : BudgetPoint) (Z : Support n) (s : R.Mode) (w : V→ℝ) (hw : ∀v,0<w v)
    {C W : ℝ} (income : 0≤C) {k : ℕ} (fixed : s.val.card≤k)
    (sold : ∀ t:R.Mode,t.val⊆s.val → (Poly.toll w t)⁻¹≤W) (rad : ℕ)
    (S : SectionData F) (Y : Hol G) (μ v κ : ℝ) :
    WilsonCapturedPrimarySoftMount.fare p Z w C rad S Y μ v κ s ≤
      (factorFee p S Y μ v κ*motion p rad k)*(((2^(2^k):ℕ):ℝ)*principal p Z W C k) := by
  let D := Push.Local.factor Y S p.supportExponent μ
  let H := hitWidth p*v/κ
  have positive (q : (parts R).Mode) : 0≤tariff p Z w C q := by
    apply mul_nonneg (Real.exp_pos _).le
    exact prod_nonneg fun j _=>mul_nonneg (inv_nonneg.mpr (prod_nonneg fun a _=>(hw a).le)) income
  have hf : 0≤factorFee p S Y μ v κ := le_max_left _ _
  have hm : 0≤ motion p rad k := by unfold motion; positivity
  have item (q : (parts R).Mode) (hq : q∈shards R s) :
      cartage p Y S μ v κ (WilsonCapturedPrimarySoftMount.cost p Z w C rad q) 0 ≤
        (factorFee p S Y μ v κ*motion p rad k)*tariff p Z w C q := by
    let scale := stage p rad (univ : Finset (Fin q.val.card))
    have hs : 0 ≤ scale := zero_le_one.trans (funded p rad _)
    calc _ = ((D+H+H*D)*scale)*tariff p Z w C q := by
              unfold cartage WilsonCapturedPrimarySoftMount.cost; dsimp only [D,H,scale]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_right
           ((mul_le_mul_of_nonneg_right (le_max_right 0 (D+H+H*D)) hs).trans
             (mul_le_mul_of_nonneg_left (width p rad k s fixed q hq) hf)) (positive q)
  calc WilsonCapturedPrimarySoftMount.fare p Z w C rad S Y μ v κ s ≤
           ∑q∈shards R s,(factorFee p S Y μ v κ*motion p rad k)*tariff p Z w C q := sum_le_sum item
       _ = (factorFee p S Y μ v κ*motion p rad k)*WilsonCapturedPrimarySoftInventory.fare p Z w C s :=
         (mul_sum ..).symm
       _ ≤ _ := mul_le_mul_of_nonneg_left (fee p Z s w hw income fixed sold) (mul_nonneg hf hm)

end YM.Integration.WilsonCapturedPrimarySoftFare
