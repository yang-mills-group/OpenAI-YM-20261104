/- Change the numerical coupling on every actual row, preserving every proper deposited face. -/
import YM.Integration.WilsonThermometerRegisteredCapturedSector

noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCapturedPace
open RG Marker Lattice Wilson QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene QuadraticLocal.Sunrise
open Push Push.Local Push.AbsoluteSums
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {V α ι:Type} [DecidableEq V] {P:Earn.Passport n V} {R:Census V}
variable (r:ℝ) (hr:0<r)
def bound:ℝ:=max 1 (max r r⁻¹)
def returned (T:Earn.Row P R G α):Earn.Row P R G α:=
  {T with salary:=r^T.lamp.lag*T.salary, sound:=mul_pos (zpow_pos hr _) T.sound,
          paint:=fun x=>(r^T.lamp.lag:ℝ)*T.paint x}
theorem evaluated (T:Earn.Row P R G α) (g:ℝ) (x:α) (U:Config G n):
    (returned r hr T).nominal g x U=T.nominal (r*g) x U:=by
  change ((r^T.lamp.lag:ℝ)*T.paint x)*(↑(g^T.lamp.lag*T.atom.unmasked U T.center):ℂ)=
    T.paint x*(↑((r*g)^T.lamp.lag*T.atom.unmasked U T.center):ℂ)
  rw [mul_zpow]
  push_cast
  ring

include hr in
private lemma roof (T:Earn.Row P R G α) (j h:ℕ) (e:T.lamp.e≤j) (a:T.lamp.toll≤h):
    r^T.lamp.lag≤(bound r)^(j+h+1):=by
  have hi:T.lamp.r≤j+h+1:=T.lamp.crest.trans (by omega)
  have one:(1:ℝ)≤bound r:=le_max_left _ _
  cases hlag:T.lamp.lag with
  | ofNat k=>
    have ku:k≤j+h+1:=by
      change (T.lamp.e:ℤ)-(T.lamp.r:ℤ)=(k:ℤ) at hlag
      omega
    change r^(k:ℤ)≤_
    rw [zpow_natCast]
    exact (pow_le_pow_left₀ hr.le ((le_max_left r r⁻¹).trans (le_max_right _ _)) _).trans
      (pow_le_pow_right₀ one ku)
  | negSucc k=>
    have ku:k+1≤j+h+1:=by
      have eq:(T.lamp.e:ℤ)-(T.lamp.r:ℤ)=-((k:ℤ)+1):=by simpa only [Loan.lag,Int.negSucc_eq] using hlag
      omega
    rw [zpow_negSucc,←inv_pow]
    exact (pow_le_pow_left₀ (inv_pos.mpr hr).le ((le_max_right r r⁻¹).trans (le_max_right _ _)) _).trans
      (pow_le_pow_right₀ one ku)

theorem original (X:ι→Earn.Row P R G α) (w:V→ℝ) (ages:V→ℕ) {σ C:ℝ} {j seats h:ℕ}
    (sold:Scene.Armada X w ages σ C j seats h):
    Scene.Armada (fun i=>returned r hr (X i)) w ages σ ((bound r)^(j+h+1)*C) j seats h:=by
  refine ⟨sold.toMinistry,sold.positive,?_,⟨fun i=>sold.purchases.spend i,fun i=>sold.purchases.usable i⟩,?_⟩
  · intro y
    have base0 : 0≤bound r:=(by norm_num:(0:ℝ)≤1).trans (le_max_left _ _)
    have weights:=budget_scale (pow_nonneg base0 (j+h+1)) (sold.suggests y)
    apply sumBudget_mono weights _ _ le_rfl
    · intro i
      dsimp only
      split_ifs
      · exact mul_nonneg (Poly.worth sold.positive _).le
          (mul_nonneg (returned r hr (X i)).sound.le (Real.exp_pos _).le)
      · exact le_rfl
    · intro i
      dsimp only
      change (if (X i).center=y then
          Poly.toll w (X i).mode*((r^(X i).lamp.lag*(X i).salary)*Real.exp (σ*(X i).length)) else 0)≤
        (bound r)^(j+h+1)*(if (X i).center=y then Poly.toll w (X i).mode*(X i).height σ else 0)
      by_cases home:(X i).center=y
      · simp only [if_pos home,Row.height]
        have e:=sold.purchases.usable i
        have term:=roof r hr (X i) j h e.1 (e.2 ▸ sold.crew _)
        convert mul_le_mul_of_nonneg_right term (show
          0≤Poly.toll w (X i).mode*((X i).salary*Real.exp (σ*(X i).length)) from
            mul_nonneg (Poly.worth sold.positive _).le (mul_nonneg (X i).sound.le (Real.exp_pos _).le)) using 1 <;> ac_rfl
      · simp [home]
  · intro i x
    change ‖(↑(r^(X i).lamp.lag):ℂ)*(X i).paint x‖≤r^(X i).lamp.lag*(X i).salary
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (zpow_pos hr _)]
    exact mul_le_mul_of_nonneg_left (sold.honor i x) (zpow_pos hr _).le
end YM.Integration.WilsonThermometerRegisteredCapturedPace
