import YM.Integration.WilsonOriginalRadialSpringRemainder
import YM.Integration.WilsonCapturedPrimaryCourse
import YM.Integration.WilsonOriginalRadialBoard

/-! The native cost of the normalized last spring differentiated on a cropped real probe. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalRadialSpringTariff
open Function Finset Filter Set Labels Lattice Wilson RG Source Next.Foundations Push.Local
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open Push.AbsoluteSums.Animals
open Planned.AtomRegular RG01.Kernel RG01.Kernel.Wheel WardBin.Lies WilsonCapturedPrimaryRough
open WilsonFirstReceivedRadialStencil WilsonCapturedPrimaryAngles WilsonCapturedPrimaryCollar
open scoped Classical BigOperators Topology
variable {G:Gauge} {d k:ℕ} {n:Side}

private theorem weight_count (o:Site n)(r:ℕ)(B:BudgetPoint)(width:B.threshold*(1+(r:ℝ))^2≤1):
    ∑ e:Link n,(if e∈active o r then B.threshold*(1+(separation e.1 o:ℝ))^2 else 0)
      ≤64*(1+(r:ℝ))^4:=by
  have h:active o r⊆ ((neighbors r o) ×ˢ (univ:Finset Axis)):=by
    intro e he
    exact mem_product.mpr ⟨(neighbors_mem r o _).mpr ((separation_comm o e.1) ▸ (mem_filter.mp he).2),mem_univ _⟩
  have hc:(active o r).card≤(r+r+1)^4*4:=by
    apply (Finset.card_le_card h).trans
    rw [card_product]
    exact Nat.mul_le_mul (neighbors_card ..) (by decide)
  calc _ ≤ ∑e:Link n,if e∈active o r then (1:ℝ) else 0:=by
              gcongr with e
              split_ifs with he
              · apply le_trans _ width
                gcongr
                · exact B.threshold_pos.le
                · exact (mem_filter.mp he).2
              · rfl
       _ = ((active o r).card:ℝ):=by simp
       _ ≤ ((r+r+1:ℕ):ℝ)^4*4:=by exact_mod_cast hc
       _ ≤ (2*(1+(r:ℝ)))^4*4:=by push_cast;gcongr;linarith
       _ = _ := by ring

def pay (G:Gauge)(k:ℕ):ℝ:=∑j∈range (k+1),|compensation G j (invoice j 1) 3|

private theorem linear (M:ℝ)(j:ℕ):compensation G j (invoice j M) 3=M*compensation G j (invoice j 1) 3:=by
  unfold compensation invoice;ring
private theorem pay_pos (G:Gauge)(k:ℕ):0≤pay G k:=sum_nonneg fun _ _=>abs_nonneg _

variable (H:History G){N p i:ℕ}
local notation "nn" => H.S.side i p

private theorem total (B:BudgetPoint)(o:Site nn)(J:Finset (Link nn))(M:ℝ)(mp:0≤M)(k:ℕ)(X:ℝ)
    (one:1≤X)(price:|probePrice (m:=i) H B o J N|≤X):
    WilsonOriginalRadialSpringRemainder.total H (N:=N) B o J k M ≤ X^k*M*pay G k:=by
  unfold WilsonOriginalRadialSpringRemainder.total pay
  rw [mul_sum]
  apply sum_le_sum
  intro j hj
  rw [linear M j,abs_mul,abs_pow,abs_mul,abs_of_nonneg mp,←mul_assoc]
  gcongr
  exact (pow_le_pow_left₀ (abs_nonneg _) price j).trans (pow_le_pow_right₀ one (Nat.lt_succ_iff.mp (mem_range.mp hj)))

def factor (H:History G)(A:Hol G)(a:Probe G d)(k:ℕ):ℝ:=
  |patterns k*baseCost G k| * (1+|panelFee A a|)^k*(65*(1+|H.levels.clock.kernel.penalty| * |tariff G|))^k*pay G k

theorem bill (A:Hol G)(B:BudgetPoint)(o:Site nn)(r:ℕ)(a:Probe G d)(k:ℕ){M:ℝ} (mp:0≤M)
    (width:B.threshold*(1+(r:ℝ))^2≤1)(beta:1≤H.β N p (i+1)):
    WilsonOriginalRadialSpringRemainder.bill H (N:=N) A B o r a k M ≤
      factor H A a k * (H.β N p (i+1))^k * (1+(r:ℝ))^((d+4)*k)*M:=by
  let u:=1+(r:ℝ)
  let β:=H.β N p (i+1)
  let Z:=1+|H.levels.clock.kernel.penalty| * |tariff G|
  let J:=active o r
  have up:1≤u:=le_add_of_nonneg_right (Nat.cast_nonneg _)
  have zp:1≤Z:=le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have bp:0≤β:=zero_le_one.trans beta
  have X:1≤(65*Z)*β*u^4:=by nlinarith only [one_le_pow₀ up (n:=4),
    mul_le_mul_of_nonneg_right (show 1≤65*Z by linarith only [zp]) bp,
    mul_le_mul_of_nonneg_right (show 1≤(65*Z)*β by nlinarith only [mul_le_mul_of_nonneg_left beta (show 0≤65*Z by linarith only [zp]),zp]) (pow_nonneg (zero_le_one.trans up) 4),beta]
  let w:ℝ:=∑e:Link nn,if e∈J then B.threshold*(1+(separation e.1 o:ℝ))^2 else 0
  have wp:0≤w:=by unfold w;exact sum_nonneg fun _ _=>ite_nonneg (mul_nonneg B.threshold_pos.le (sq_nonneg _)) le_rfl
  have wc:w≤64*u^4:=weight_count o r B width
  have sc:1+w≤65*u^4:=by linarith only [wc,one_le_pow₀ up (n:=4)]
  have fc:|1+|β*H.levels.clock.kernel.penalty| * tariff G| ≤ Z*β:=by
    calc _ ≤ 1+β*|H.levels.clock.kernel.penalty| * |tariff G|:=by
                simpa only [abs_one,abs_mul,abs_abs,abs_of_nonneg bp] using
                  (abs_add_le 1 (|β*H.levels.clock.kernel.penalty| * tariff G))
         _ ≤ Z*β:=by dsimp [Z];linarith only [beta]
  have prior:|probePrice (m:=i) H (quadratic B) o J N|≤(65*Z)*β*u^4:=by
    change |(1+|β*H.levels.clock.kernel.penalty| * tariff G)*(1+w)|≤_
    rw [abs_mul,abs_of_nonneg (show 0≤1+w by linarith only [wp])]
    calc _ ≤ (Z*β)*(65*u^4):=mul_le_mul fc sc (by linarith only [wp]) (mul_nonneg (zero_le_one.trans zp) bp)
         _ = _ :=by ring
  have unit:wallet A a r≤(1+|panelFee A a|)*u^d:=by
    unfold wallet;change 1+panelFee A a*u^d≤_
    nlinarith only [mul_le_mul_of_nonneg_right (le_abs_self (panelFee A a)) (pow_nonneg (zero_le_one.trans up) d),one_le_pow₀ up (n:=d)]
  have pk:0≤patterns k*baseCost G k:=mul_nonneg (patterns_nonneg _) (baseCost_nonneg ..)
  have cap:=total H (N:=N) (quadratic B) o J M mp k _ X prior
  calc WilsonOriginalRadialSpringRemainder.bill H (N:=N) A B o r a k M
      = (patterns k*baseCost G k)*(wallet A a r)^k * WilsonOriginalRadialSpringRemainder.total H (N:=N) (quadratic B) o J k M:=by
            unfold WilsonOriginalRadialSpringRemainder.bill WilsonCapturedPrimaryRough.price;ring
    _ ≤ (|patterns k*baseCost G k| * ((1+|panelFee A a|)*u^d)^k)*(((65*Z)*β*u^4)^k*M*pay G k):= by
          apply mul_le_mul _ cap
          · exact sum_nonneg fun _ _=>abs_nonneg _
          · positivity
          rw [abs_of_nonneg pk]
          gcongr
          · exact zero_le_one.trans (wallet_one ..)

    _ = _ :=by unfold factor;change _=_*β^k*u^((d+4)*k)*M
               rw [Nat.add_mul,pow_add]
               simp only [Z,mul_pow,←pow_mul];ring

end YM.Integration.WilsonOriginalRadialSpringTariff
