import YM.MS.Dial.Watch
import YM.FVAAlt2.Shop.Menus
import YM.Pert.Scale.Engineering
import YM.Extra.FREE_DETECTOR_ALGEBRA.Corridors
import YM.RG12.Strike.Stock

set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonRichContinuumTree
open Function Set Filter Finset Maxwell Maxwell.Wick Labels Extra.FD
open MS MS.Local.Physical MS.Land MS.Book MS.Book.Program MS.Rake
open scoped Topology ContDiff Classical BigOperators

variable {G : Gauge} {B : Deck G} {A : Booked B}

def placement : E4 →L[ℝ] Points 2 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => E4)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin 2 => if i=0 then ContinuousLinearMap.id ℝ E4 else 0))

theorem at_index (z : E4) (i : Fin 2) : placement z i = if i=0 then z else 0 := by
  by_cases h : i=0 <;> simp [placement,h]

theorem separate {z : E4} (hz : z≠0) : placement z ∈ conf 2 := by
  intro i j e
  change placement z i = placement z j at e
  fin_cases i <;> fin_cases j <;> simp_all [at_index]

def bill (p : Fin 2 → Rake.Label B) := ∑ i, (p i).h

theorem degree (v : Rake.Label B) :
    Exact (Maxwell.reduceEq (Milk.Lightning v)) v.h := by
  have h := (pure_grade _ _).mp (FVAAlt2.Shop.isSeated B v.item.2)
  apply gradeMove generation costKey Maxwell.reduceEq (gradientReduce (·+2))
  intro i hi
  exact congrArg Prod.fst ((weight_slot i).symm.trans (h hi))

def tree (M : MS_Data G A) (p : Fin 2 → Rake.Label B) (u : ℝ) (z : E4) :=
  Dial.tour M p u (fun i => Theater.out (placement z i)) univ 0

def kernel (p : Fin 2 → Rake.Label B) (z : E4) :=
  moment G (placement z) (fun i => Maxwell.reduceEq (Milk.Lightning (p i)))

theorem original (M : MS_Data G A) (p : Fin 2 → Rake.Label B) (u : ℝ) {z : E4} (hz : z≠0) :
    tree M p u z = kernel p z :=
  Dial.highest_zero M u (placement z) p (separate hz)

theorem radial (p : Fin 2 → Rake.Label B) {z : E4} (hz : z≠0) {t : ℝ} (ht : 0<t) :
    kernel p (t•z) = (t:ℂ)^(-(bill p:ℤ)) * kernel p z := by
  have h := Pert.Scale.rising_moment (separate hz) (fun i => degree (p i)) ht.ne'
  rw [MultilinearMap.map_smul_univ,Finset.prod_pow_eq_pow_sum,smul_eq_mul] at h
  change (t:ℂ)^(bill p) * moment G (t•placement z) _ = kernel p z at h
  have hn : (t:ℂ)^bill p ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ht.ne')
  rw [zpow_neg,zpow_natCast,←h,←mul_assoc,inv_mul_cancel₀ hn,one_mul]
  simp only [kernel,map_smul]

theorem garden (M : MS_Data G A) (p : Fin 2 → Rake.Label B) (u : ℝ) (a : ℂ) :
    RG12.Strike.Garden (fun z => a * tree M p u z) (bill p) := by
  constructor
  · intro z hz
    have hn : z≠0 := hz
    obtain ⟨X⟩ := EnhMoment (fun i => Maxwell.reduceEq (Milk.Lightning (p i)))
    have hk : ContDiffAt ℝ ω (kernel p) z :=
      (foreground X (separate hn)).comp z placement.contDiff.contDiffAt
    apply contDiffAt_const.mul
    apply hk.congr_of_eventuallyEq
    filter_upwards [IsOpen.mem_nhds isOpen_compl_singleton hn] with y hy
    exact original M p u hy
  · intro z hz t ht
    change a * tree M p u (t•z) = (t:ℂ)^(-(bill p:ℤ)) * (a * tree M p u z)
    rw [original M p u (smul_ne_zero ht.ne' hz),original M p u hz,radial p hz ht]
    ring

/-- Every local first-field coefficient multiplies the genuine tree by a fixed signed scalar.
Its entire annular change consists of the lower engineering power, and is zero at equal height. -/
theorem change (M : MS_Data G A) (p : Fin 2 → Rake.Label B) (u : ℝ) (a : ℂ)
    {d : ℕ} (hd : bill p ≤ d) {z : E4} (hz : z≠0) {t : ℝ} (ht : 0<t) :
    (t:ℂ)^d * (a*tree M p u (t•z)) - a*tree M p u z =
      (a*tree M p u z) * ((t:ℂ)^(d-bill p)-1) := by
  rw [(garden M p u a).radial hz ht]
  have hn : (t:ℂ)^bill p≠0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ht.ne')
  have he : (t:ℂ)^d = (t:ℂ)^(d-bill p)*(t:ℂ)^bill p := by rw [←pow_add,Nat.sub_add_cancel hd]
  rw [he,inv_pow]
  field_simp

end YM.Integration.WilsonRichContinuumTree

