import YM.Integration.WilsonMeasuredPublicEntranceTrialOwnerCoupon
import YM.Integration.WilsonOriginalFlatHaloRate

/-! The common scalar on an actual bought older housing. It is independent
of the owner, of the chosen physical or trial peers, and of their wage. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceCropRoof
open Finset Filter Lattice Wilson RG Labels Source Marker QuadraticLocal Ac Multi
open PhysicalNext PhysicalNext.Repeat Legato Push.Local Push.AbsoluteSums
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedCorridor
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){V:Type}[DecidableEq V]{J:Census V}
def area (r l:ℕ):ℝ:=(2:ℝ)^r*(2*(((2^(2^r):ℕ):ℝ)*Real.exp (102*(l:ℝ)))*r*Real.exp r)
def roof (s:J.Mode)(l:ℕ):ℝ:=(shards J s).card+4*(1+area s.val.card l)

private theorem area_paid {n:Side}(P:BudgetPoint)(Z:Support n)(r l:ℕ)(point:P.supportExponent ≤ 100)
    (room:coverNumber P.B Z ≤ l):WilsonOriginalFlatOccupiedRate.bill P Z 1 r ≤ area r l:=by
  unfold WilsonOriginalFlatOccupiedRate.bill WilsonOriginalFlatOccupiedRate.roof area
  simp only [max_self,one_pow,mul_one]
  have mul: (P.supportExponent+2)*(coverNumber P.B Z:ℝ) ≤ 102*(l:ℝ):=
    mul_le_mul (by linarith only [point]) (by exact_mod_cast room) (Nat.cast_nonneg _) (by norm_num)
  gcongr

omit [DecidableEq V] in
private theorem capped {b f:ℕ}(bc:b ≤ f)(w:V → ℝ)(w₁:∀v,w v ≤ 1):
    ∀v,wallet R w bc v ≤ 1:=by
  refine Nat.decreasingInduction (motive:=fun j jt=>∀v,wallet R w jt v ≤ 1) ?_ ?_ bc
  · intro j jj prev v
    rw [show wallet R w jj.le=Stoop.radius (wallet R w jj) (factor R j) from Nat.decreasingInduction_succ_left ..]
    change wallet R w jj v/factor R j ≤ 1
    exact (div_le_one (zero_lt_one.trans_le (le_max_left ..))).mpr ((prev v).trans (le_max_left ..))
  · rw [show wallet R w (le_refl f)=w from Nat.decreasingInduction_self ..];exact w₁

theorem calendar (simple:G.Simple):
    ∀ᶠ b:ℕ in atTop,R.alloy.B.a.clock.hatBeta b*LocalComparison.forcedDivisor R.family b ≤ 1:=by
  simpa only [pow_zero,div_one] using (WilsonOriginalFlatHaloRate.calendar R simple 0 (tol:=1) zero_lt_one).mono
    (fun _ q=>q.2)

theorem original {p b f:ℕ}(bc:b ≤ f)(W:Rep G (R.family.side b p))(Z:Support (R.family.side b p))
    (l:ℕ)(s:J.Mode)(w:V → ℝ)(v:V)(C M:ℝ)(w₀:∀i,0<w i)(w₁:∀i,w i ≤ 1)
    (point:W.p.supportExponent ≤ 100)(room:coverNumber W.p.B Z ≤ l)
    (hal:R.alloy.B.a.clock.hatBeta b*LocalComparison.forcedDivisor R.family b ≤ 1):
    let realW:=Stoop.radius w (WilsonMeasuredPublicEntranceOwnerWallet.divisor w v C M)
    let tally:=Poly.toll (wallet R realW bc) s
    (shards J s).card+4*(tally+WilsonOriginalFlatOccupiedRate.bill W.p Z 1 s.val.card)*R.alloy.B.a.clock.hatBeta b*
      LocalComparison.forcedDivisor R.family b ≤ roof s l:=by
  intro realW tally
  have div:1 ≤ WilsonMeasuredPublicEntranceOwnerWallet.divisor w v C M:=(le_max_left ..).trans (le_max_left ..)
  have rp:∀i,0<realW i:=fun i=>div_pos (w₀ i) (zero_lt_one.trans_le div)
  have rc:∀i,realW i ≤ 1:=fun i=>(div_le_one (zero_lt_one.trans_le div)).mpr ((w₁ i).trans div)
  have all:=capped R bc realW rc
  have pos:=WilsonOriginalOccupiedCorridor.positive R realW rp bc
  have low:0 ≤ tally:=Finset.prod_nonneg fun i _=>(pos i).le
  have wage:tally ≤ 1:=Finset.prod_le_one (fun i _=>(pos i).le) (fun i _=>all i)
  have lit:0 ≤ WilsonOriginalFlatOccupiedRate.bill W.p Z 1 s.val.card:=by
    unfold WilsonOriginalFlatOccupiedRate.bill WilsonOriginalFlatOccupiedRate.roof;positivity
  have bound:=area_paid W.p Z s.val.card l point room
  unfold roof
  have rate:=mul_le_of_le_one_right (show 0 ≤ 4*(tally+WilsonOriginalFlatOccupiedRate.bill W.p Z 1 s.val.card) by positivity) hal
  linarith only [rate,wage,bound,mul_assoc (4*(tally+WilsonOriginalFlatOccupiedRate.bill W.p Z 1 s.val.card))
    (R.alloy.B.a.clock.hatBeta b) (LocalComparison.forcedDivisor R.family b)]

end YM.Integration.WilsonMeasuredPublicEntranceCropRoof
end
