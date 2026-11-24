import YM.Integration.WilsonOriginalObservedRoseSevenScale
import YM.Integration.WilsonOlderFreshSoftSocketStationPanelWindow
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationSevenPower
open Finset WilsonOriginalObservedRoseMeshHeight WilsonOriginalObservedRoseVanePurse
open WilsonPositionThermometerConnected
open scoped BigOperators
local notation "Face" => Finset (Fin 3)

def order (target bank mesh:ℕ):ℕ:=3*(bank+1)+mesh*14+target+1

theorem original {θ g r fee:ℝ}(hot:0<θ)(clear:21≤θ⁻¹)(gp:0≤g)(ratio:g≤4*θ)
    (rp:0≤r)(small:r≤1)(cp:0≤fee)(target bank mesh due:ℕ)(debt:due+1≤bank)
    (cost:fee*(4:ℝ)^order target bank mesh≤θ⁻¹)(old stopped:Face→ℂ)
    (gross:∀s:Face,s.Nonempty → r^(height ages s)*‖old s‖≤2*(θ⁻¹)^(bank+mesh*height ages s))
    (feePaid:∀s:Face,s.Nonempty → ‖old s-stopped s‖≤fee*(θ⁻¹)^due*g^order target bank mesh):
    r^14*‖value old-value stopped‖≤θ^target:=by
  let z:=θ⁻¹
  let p:=order target bank mesh
  have one:1≤z:=(by norm_num : (1:ℝ)≤21).trans clear
  have three:3≤z:=(by norm_num : (3:ℝ)≤21).trans clear
  have eight:21*θ≤1:=(le_div_iff₀ hot).mp (by simpa only [one_div] using clear)
  have cool:θ≤1:=by linarith
  have collect:z*θ=1:=inv_mul_cancel₀ hot.ne'
  have native:∀s:Face,s.Nonempty → r^(height ages s)*‖old s-stopped s‖≤z^(bank+mesh*height ages s)*θ^p:=by
    intro s hs
    have rsmall:r^(height ages s)≤1:=pow_le_one₀ rp small
    calc
      _≤‖old s-stopped s‖:=mul_le_of_le_one_left (norm_nonneg _) rsmall
      _≤fee*z^due*g^p:=feePaid s hs
      _≤fee*z^due*((4*θ)^p):=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ gp ratio _) (mul_nonneg cp (pow_nonneg (inv_nonneg.mpr hot.le) _))
      _=(fee*4^p)*z^due*θ^p:=by rw[mul_pow];ring
      _≤z*z^due*θ^p:=by gcongr
      _≤z^(bank+mesh*height ages s)*θ^p:=by
        rw [mul_comm z (z^due),←pow_succ]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one (by omega)) (pow_nonneg hot.le _)
  have cut:∀s:Face,s.Nonempty → r^(height ages s)*‖stopped s‖≤z^(bank+1+mesh*height ages s):=by
    intro s hs
    let a:=bank+mesh*height ages s
    have zero:0≤z^a:=pow_nonneg (zero_le_one.trans one) _
    have triangle:‖stopped s‖≤‖old s‖+‖old s-stopped s‖:=by
      rw [←norm_neg (old s-stopped s),neg_sub]
      calc _=‖old s+(stopped s-old s)‖:=by rw[add_sub_cancel]
           _≤_:=norm_add_le .. 
    have gap:=native s hs
    have upper:=gross s hs
    calc
      _≤r^(height ages s)*(‖old s‖+‖old s-stopped s‖):=mul_le_mul_of_nonneg_left triangle (pow_nonneg rp _)
      _≤2*z^a+z^a*θ^p:=by rw[mul_add];exact add_le_add upper gap
      _≤3*z^a:=by nlinarith only [mul_le_of_le_one_right zero ((show θ^p≤1 from pow_le_one₀ hot.le cool))]
      _≤z*z^a:=mul_le_mul_of_nonneg_right three zero
      _=z^(bank+1+mesh*height ages s):=by rw [mul_comm,←pow_succ];congr 1;dsimp [a];omega
  have bound:=WilsonOriginalObservedRoseSevenScale.original old stopped rp one (pow_nonneg hot.le p) mesh (bank+1)
    (fun s hs=>by
      apply (gross s hs).trans
      rw [show bank+1+mesh*height ages s=bank+mesh*height ages s+1 by omega,pow_succ,mul_comm]
      exact mul_le_mul_of_nonneg_left ((by norm_num : (2:ℝ)≤3).trans three) (pow_nonneg (zero_le_one.trans one) _))
    cut (fun s hs=>(native s hs).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one (by omega)) (pow_nonneg hot.le p)))
  let d:=3*(bank+1)+mesh*14
  have both:z^d*θ^d=1:=by rw [←mul_pow,collect,one_pow]
  calc
    _≤21*z^d*θ^p:=bound
    _=(21*θ)*(z^d*θ^d)*θ^target:=by change _*(θ^((d+target)+1))=_;rw[pow_succ,pow_add];ring
    _≤θ^target:=by rw [both,mul_one];exact mul_le_of_le_one_left (pow_nonneg hot.le _) eight

end YM.Integration.WilsonOlderFreshSoftSocketStationSevenPower
end
