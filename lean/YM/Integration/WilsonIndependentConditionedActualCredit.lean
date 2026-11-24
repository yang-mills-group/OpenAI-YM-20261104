import YM.WilsonCoeffUV.Auxiliary.Plates
import YM.Integration.WilsonAddressedCollarWindow
import YM.Integration.WilsonOriginalPublicRelativeGramKineticMesh
import YM.Integration.WilsonIndependentConditionedBankFittedFees

/-! The three cash ages on the original optical collar are bounded by one linear function of the reporting log, before either finite regulator is named. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedActualCredit
open Filter Real Function Lattice Wilson RG RG.Supply Precision PhysicalNext.Repeat.Legato
open Next.Rank
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol Extra.Histories
open WilsonIndependentConditionedBankFittedFees (age)
open WilsonInvariantActionPosition (berth)
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
open scoped Topology Classical
variable {G:Gauge}(R:Run G)
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta

def badge (f:ℕ):ℝ:=log (β f)
def gramAge (f K:ℕ):ℝ:=zz A f+2*(R.family.path.levels.S.scale K-R.family.path.levels.S.scale f)

def drift (t:ℕ):Credit:=
  ⟨1,2+(t+1)*(2+(log 3)⁻¹),by
    have z:0 < log 3:=log_pos (by norm_num)
    have x:0 ≤ ((t:ℝ)+1)*(2+(log 3)⁻¹):=by positivity
    linarith⟩

theorem homes (f:ℕ):age R f f=zz A f:=by simp [age]

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(t:ℕ):
    ∀ᶠ f:ℕ in atTop,let K:=berth R t f;let S:=(drift t).buy (badge R f)
      1 ≤ badge R f ∧ 1 ≤ age R f f ∧ age R f f ≤ S ∧
      1 ≤ age R f K ∧ age R f K ≤ S ∧ 1 ≤ gramAge R f K ∧ gramAge R f K ≤ S:=by
  have leads:=Station.hat_rate A simple
  filter_upwards [WilsonAddressedCollarWindow.original R simple slow t (η:=1) zero_lt_one,
    (tendsto_log_atTop.comp leads).eventually_ge_atTop 1] with f edge warm
  let K:=berth R t f
  let gap:=R.family.path.levels.S.scale K-R.family.path.levels.S.scale f
  have up:f ≤ K:=edge.1.le
  have hp:0<β f:=zero_lt_one.trans (R.family.path.levels.fits.delayed f)
  have q:1 ≤ badge R f:=warm
  have hz:1 ≤ zz A f:=by
    change 1 ≤ 1+log (badge R f)
    linarith [log_nonneg q]
  have z:zz A f ≤ 2*badge R f:=by
    change 1+log (badge R f) ≤ _
    linarith [log_le_self (zero_le_one.trans q)]
  have upper:gap ≤ (t+1)*badge R f:=by
    have h:=log_le_log (div_pos (R.family.S.a_pos f) (R.family.S.a_pos K)) edge.2.2
    rw [rpow_one,log_mul (pow_pos hp t).ne' hp.ne',log_pow] at h
    have exactGap:gap=log (R.family.S.a f/R.family.S.a K):=by
      change R.family.S.scale K-R.family.S.scale f=_
      rw [Schedule.scale,Schedule.scale,log_inv,log_inv,
        log_div (R.family.S.a_pos f).ne' (R.family.S.a_pos K).ne']
      ring
    rw [exactGap]
    simpa only [badge,add_mul,one_mul] using h
  have lpos:0 < log (3:ℝ):=log_pos (by norm_num)
  have nbar:((K-f:ℕ):ℝ)*log 3 ≤ gap:=by
    simpa only [show f+(K-f)=K by omega] using AuxPlates.scaleTape R.family.path.levels.S f (K-f)
  have day:((K-f:ℕ):ℝ) ≤ ((t+1)*badge R f)*(log 3)⁻¹:=by
    simpa only [div_eq_mul_inv] using (le_div_iff₀ lpos).mpr (nbar.trans upper)
  have inc:0 ≤ gap:=(mul_nonneg (Nat.cast_nonneg _) lpos.le).trans nbar
  have base:0 ≤ ((t:ℝ)+1)*badge R f:=mul_nonneg (by positivity) (zero_le_one.trans q)
  have extra:0 ≤ ((t:ℝ)+1)*badge R f*(log 3)⁻¹:=mul_nonneg base (inv_nonneg.mpr lpos.le)
  have fee:(drift t).buy (badge R f) =
      2*badge R f+2*((t+1)*badge R f)+((t+1)*badge R f)*(log 3)⁻¹:=by
    simp only [drift,Credit.buy,pow_one];ring
  change 1 ≤ badge R f ∧ 1 ≤ age R f f ∧ age R f f ≤ _ ∧ 1 ≤ age R f K ∧
    age R f K ≤ _ ∧ 1 ≤ gramAge R f K ∧ gramAge R f K ≤ _
  rw [homes,fee]
  change _ ∧ _ ∧ _ ∧ 1 ≤ zz A f+gap+((K-f:ℕ):ℝ) ∧ _ ∧ 1 ≤ zz A f+2*gap ∧ _
  refine ⟨q,hz,by linarith only [z,base,extra],by linarith only [hz,inc,Nat.cast_nonneg (α:=ℝ) (K-f)],
    ?_,by linarith only [hz,inc],?_⟩
  · change zz A f+gap+((K-f:ℕ):ℝ) ≤ _
    linarith only [z,upper,day,base]
  · change zz A f+2*gap ≤ _
    linarith only [z,upper,extra]

theorem polynomial (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(t:ℕ)(T:Credit):
    ∀ᶠ f:ℕ in atTop,let K:=berth R t f;let M:=(T.usingC (drift t)).buy (badge R f)
      T.buy (age R f f) ≤ M ∧ T.buy (age R f K) ≤ M ∧ T.buy (gramAge R f K) ≤ M:=by
  filter_upwards [original R simple slow t] with f h
  dsimp only
  rw [Credit.stock_up]
  exact ⟨T.elder h.2.1 h.2.2.1,T.elder h.2.2.2.1 h.2.2.2.2.1,
    T.elder h.2.2.2.2.2.1 h.2.2.2.2.2.2⟩

theorem subpower (simple:G.Simple)(T:Credit){ε:ℝ}(ep:0<ε):
    ∀ᶠ f:ℕ in atTop,T.buy (badge R f) ≤ (thermal R f)^(-ε):=by
  have raw:=(isLittleO_log_rpow_rpow_atTop (T.d:ℝ) (show 0<ε/2 by positivity)).def
    (inv_pos.mpr (zero_lt_one.trans_le T.good))
  have leads:=Station.hat_rate A simple
  filter_upwards [leads.eventually raw,(tendsto_log_atTop.comp leads).eventually_ge_atTop 1] with f heard high
  have bp:0 < β f:=zero_lt_one.trans (R.family.path.levels.fits.delayed f)
  have logpos:0 ≤ log (β f):=zero_le_one.trans high
  change ‖(log (β f))^(T.d:ℝ)‖ ≤ T.x⁻¹*‖(β f)^(ε/2)‖ at heard
  rw [rpow_natCast,norm_eq_abs,abs_of_nonneg (pow_nonneg logpos _),norm_eq_abs,
    abs_of_pos (rpow_pos_of_pos bp _)] at heard
  have pay:=mul_le_mul_of_nonneg_left heard (zero_le_one.trans T.good)
  have paid:T.buy (badge R f) ≤ (β f)^(ε/2):=by
    simpa only [Credit.buy,badge,←mul_assoc,mul_inv_cancel₀ (zero_lt_one.trans_le T.good).ne',one_mul] using pay
  have price:(thermal R f)^(-ε)=(β f)^(ε/2):=by
    change ((sqrt (β f))⁻¹)^(-ε)=(β f)^(ε/2)
    rw [inv_rpow (sqrt_nonneg _) _,sqrt_eq_rpow,←rpow_mul bp.le,←rpow_neg bp.le]
    congr 1
    ring
  simpa only [price] using paid

end YM.Integration.WilsonIndependentConditionedActualCredit
