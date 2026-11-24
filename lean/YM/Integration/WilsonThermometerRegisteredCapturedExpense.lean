import YM.Integration.WilsonThermometerRegisteredCapturedRoster
import YM.Integration.WilsonThermometerRegisteredCapturedOffers

/-! The exact receipt for one genuine compound ordinary row, before testing
its scalar source. Original salaries are counted at their physical path width. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCapturedExpense
open RG QuadraticLocal QuadraticLocal.Earn Lattice Wilson Marker
open WilsonThermometerRegisteredCapturedRoster
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {V α ξ:Type*} [DecidableEq V]
variable {P:Earn.Passport n V} {R:Census V} {B:Earn.Passport n Unit} {D:Census Unit}
local notation "Old" => Earn.Row P R G α
private def inside (a:List Old):ℕ:=(a.map fun j=>j.atom.length).sum
private def reach (a:List Old):ℕ:=(a.map fun j=>j.length).sum

private lemma bounded (a:List Old) : inside a ≤ reach a:=by
  induction a with
  | nil=>rfl
  | cons z a h=>
    change z.atom.length+inside a≤z.length+reach a
    exact Nat.add_le_add (Nat.le_add_left ..) h

private lemma paths (w:V→Walk) (a:List Old) : (atom w a).length=extra w a+inside a :=by
  induction a with
  | nil=>change (∑ i:Fin 0,_) = 0+0; simp
  | cons z a h=>
    change (WilsonThermometerRegisteredCapturedWords.joined
      (WilsonThermometerRegisteredCapturedWords.move (w z.binder.front) z.atom) (atom w a)).length =
      (z.lamp.r*(w z.binder.front).length+extra w a)+(z.atom.length+inside a)
    rw [WilsonThermometerRegisteredCapturedWords.length,WilsonThermometerRegisteredCapturedWords.reach,h]
    omega

private lemma height (a:List Old) (σ:ℝ):
    (a.map fun j=>j.height σ).prod = wages a*Real.exp (σ*(reach a:ℝ)) := by
  induction a with
  | nil=>simp [wages,reach]
  | cons z a h=>
    change z.height σ*(a.map fun j=>j.height σ).prod=(z.salary*wages a)*Real.exp (σ*((z.length+reach a:ℕ):ℝ))
    rw [h,Nat.cast_add,mul_add,Real.exp_add]
    unfold Row.height
    ring

theorem capacity (w:V→Walk) (K:ℕ) (b:∀v,(w v).length≤K) (a:List Old):
    extra w a ≤ angularRank a*K := by
  induction a with
  | nil=>simp [extra,angularRank]
  | cons z a h=>
    change z.lamp.r*(w z.binder.front).length+extra w a≤(z.lamp.r+angularRank a)*K
    rw [Nat.add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (b _)) h

theorem original (w:V→Walk) (S:Earn.Binder B D) (a:List Old) (d:ℕ) (hd:0<d)
    (limit:allowed a≤d+1) (σ:ℝ) (t:α) (χ:ℂ) (test:ξ→ℂ)
    (K rankCap:ℕ) (leσ:0≤σ) (b:∀v,(w v).length≤K) (cap:angularRank a≤rankCap):
    (row w S a d hd limit σ t χ test).height σ ≤
      (max 1 ‖χ‖*Real.exp (σ*((S.length+2*rankCap*K:ℕ):ℝ)))*(a.map fun j=>j.height σ).prod := by
  have e:extra w a≤rankCap*K:=(capacity w K b a).trans (Nat.mul_le_mul_right _ cap)
  have compare:extra w a + (S.length+(atom w a).length)≤ S.length+2*rankCap*K+reach a:=by
    rw [paths,Nat.mul_assoc 2 rankCap K]
    have h:=bounded a
    omega
  have win:=Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ)|>.mpr compare) leσ)
  have gold:0≤wages a:=by
    unfold wages
    apply List.prod_nonneg
    intro z hz
    rcases List.mem_map.mp hz with ⟨j,_,rfl⟩
    exact j.sound.le
  have paid:=mul_le_mul_of_nonneg_left win (mul_nonneg (le_trans (by norm_num:0≤(1:ℝ)) (le_max_left (1:ℝ) ‖χ‖)) gold)
  have split (m n:ℕ): Real.exp (σ*((m+n:ℕ):ℝ))=Real.exp (σ*(m:ℝ))*Real.exp (σ*(n:ℝ)):=by
    rw [Nat.cast_add,mul_add,Real.exp_add]
  rw [split (extra w a) (S.length+(atom w a).length),split (S.length+2*rankCap*K) (reach a)] at paid
  rw [height]
  change Real.exp (σ*(extra w a:ℝ))*max 1 ‖χ‖*wages a*Real.exp (σ*((S.length+(atom w a).length:ℕ):ℝ))≤_
  convert paid using 1 <;> ac_rfl

end YM.Integration.WilsonThermometerRegisteredCapturedExpense
