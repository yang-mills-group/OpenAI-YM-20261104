import YM.Integration.WilsonAllDateHarvestFixedOriginHousing
import YM.Integration.WilsonReportHarvestReplayIncome

/-! After an observation scale and a physical distance have been chosen, the
true terminal cutoff covers both the original lower interval and a finite
period-independent multiplier. The source remains the original cutoff palette. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestFixedOriginInvoice
open Filter Lattice Wilson RG Marker PhysicalNext.Repeat.Legato RG05Readout.Many
open private triple from YM.Integration.WilsonReportHarvestReplayIncome
open WilsonReportHarvestReplayPhysical
open scoped Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "CF" => R.family
local notation "A" => R.family.path.levels
local notation "S" => R.family.S

def engineering (d:ℕ):ℕ:=2*WilsonReportHarvestReplayIncome.engineering d+1

include simple in
theorem amount_le {ε:ℝ} (positive:0<ε) (small:ε ≤ 1):
    ∀ᶠm:ℕ in atTop,∀j:ℕ,m ≤ j→∀N:ℕ,j ≤ N→∀per n p e l:ℕ,
      let g:=(Real.sqrt ((CF).path.rep N per j).beta)⁻¹
      let δ:=amount R n m j N per p e l ε
      0<g ∧ g ≤ 1 ∧ 0<δ ∧ δ ≤ 1 := by
  filter_upwards [(Next.Rank.Station.hat_rate (A) simple).eventually_ge_atTop 2] with m base j mj N jN per n p e l g δ
  have x:1 ≤ (A).clock.hatBeta j:=((A).fits.delayed j).le
  have two:2 ≤ (A).clock.hatBeta j:=base.trans (beta_le' (C:=CF) simple mj)
  have band:(A).clock.hatBeta j/2 ≤ ((CF).path.rep N per j).beta:=(R.makes.wilson.represents N per j jN).band.1
  have low:1 ≤ ((CF).path.rep N per j).beta:=(show 1 ≤ (A).clock.hatBeta j/2 by linarith only [two]).trans band
  have root:1 ≤ Real.sqrt ((CF).path.rep N per j).beta:=by
    calc 1 = Real.sqrt (1:ℝ):=by norm_num
         _ ≤ _:=Real.sqrt_le_sqrt low
  have gp:0<g:=inv_pos.mpr (zero_lt_one.trans_le root)
  have g1:g ≤ 1:=inv_le_one_of_one_le₀ root
  have mesh:1 ≤ (S).a m/(S).a j:=(one_le_div ((S).a_pos j)).2 ((S).strictAnti.antitone mj)
  have v:=mul_nonneg positive.le (pow_nonneg gp.le p)
  have ub0:1 ≤ ((S).a m/(S).a j)^e:=one_le_pow₀ mesh
  have ub1:1 ≤ ((A).clock.hatBeta j)^(l*(j-n+1)):=one_le_pow₀ x
  refine ⟨gp,g1,div_pos (div_pos (mul_pos positive (pow_pos gp p)) (zero_lt_one.trans_le ub0)) (zero_lt_one.trans_le ub1),?_⟩
  calc δ ≤ ε*g^p/((S).a m/(S).a j)^e:=div_le_self (div_nonneg v (zero_le_one.trans ub0)) ub1
       _ ≤ ε*g^p:=div_le_self v ub0
       _ ≤ 1:=mul_le_one₀ small (pow_nonneg gp.le p) (pow_le_one₀ gp.le g1)

include simple in
theorem original (d h k p:ℕ) {ε:ℝ} (ep:0<ε):
    ∀ᶠm:ℕ in atTop,∀n:ℕ,n ≤ m→∀charge:ℝ,1 ≤ charge→∀ᶠj:ℕ in atTop,
      m ≤ j ∧ m-n ≤ j-m ∧ n<j ∧ ∀per:ℕ,
      let N:=j+1
      let g:=(Real.sqrt ((CF).path.rep N per j).beta)⁻¹
      let a:=(S).a m/(S).a j
      let Q:=allowance R m N d h
      let δ:=amount R n m j N per p (engineering d) (WilsonReportHarvestReplayIncome.reserve 0 d h k) (ε/2)
      1 ≤ Q ∧ 2*δ * (WilsonAllDateHarvestIntervalPrice.bill CF n j (d+1) k (Q*a))^3 ≤ ε*g^p/charge := by
  filter_upwards [WilsonReportHarvestUpperRange.original R simple d h] with m issued n nm charge cash
  filter_upwards [WilsonAllDateHarvestFixedOriginHousing.schedule (CF) n m charge,eventually_gt_atTop m]
    with j reach later
  obtain ⟨mj,mature,old,available⟩:=reach
  refine ⟨mj,mature,nm.trans_lt later,?_⟩
  intro per N g a Q δ
  let x:=(A).clock.hatBeta j
  let σ:=(S).a n/(S).a j
  let u:=2*(d+2)
  let v:=WilsonReportHarvestReplayIncome.reserve 0 d h k
  let b:=WilsonAllDateHarvestIntervalPrice.bill CF n j (d+1) k (Q*a)
  have xp:1 ≤ x:=((A).fits.delayed j).le
  have ap:1 ≤ a:=(one_le_div ((S).a_pos j)).2 ((S).strictAnti.antitone mj)
  have a0:=zero_le_one.trans ap
  have x0:=zero_le_one.trans xp
  have a2:a ≤ a^2:=by simpa only [pow_one] using pow_le_pow_right₀ ap (by norm_num:1 ≤ 2)
  have σ0:0 ≤ σ:=div_nonneg ((S).a_pos n).le ((S).a_pos j).le
  have ⟨fac,ceiling,_⟩:=issued j mj j mj le_rfl (WilsonReportHarvestUpperRange.latest (S) mj)
  have Q1:1 ≤ Q:=one_le_mul_of_one_le_of_one_le (one_le_pow₀ ((A).fits.delayed m).le) fac
  have upper:Q ≤ x^h*((a^2)^u*x^u) :=
    mul_le_mul (pow_le_pow_left₀ (zero_lt_one.trans ((A).fits.delayed m)).le (beta_le' (C:=CF) simple mj) h)
      (ceiling.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ a0 a2 u) (pow_nonneg x0 u)))
      (zero_le_one.trans fac) (pow_nonneg x0 h)
  have room:σ ≤ x^(2*(0+3))*a^2:=by
    calc σ = ((S).a n/(S).a m)*a:=by dsimp only [σ,a];field_simp [((S).a_pos m).ne']
         _ ≤ a*a:=mul_le_mul_of_nonneg_right old a0
         _ = a^2:=(sq a).symm
         _ ≤ _:=le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ xp)
  have top:=triple xp (one_le_pow₀ ap : 1 ≤ a^2) (zero_le_one.trans Q1) σ0 0 d h k (j-n) upper room
  have b0:0 ≤ b:=by
    dsimp only [b,WilsonAllDateHarvestIntervalPrice.bill]
    exact mul_nonneg (mul_nonneg (pow_nonneg x0 _) (mul_nonneg (zero_le_one.trans Q1) a0)) (pow_nonneg σ0 _)
  have base:b ≤ x^((3*k+4)*(j-n)+k)*(Q*a^2)*σ^(d+1):=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left a2 (zero_le_one.trans Q1))
      (pow_nonneg x0 _)) (pow_nonneg σ0 _)
  have invoice:charge*b^3 ≤ a^(engineering d)*x^(v*(j-n+1)) :=
    (mul_le_mul available ((pow_le_pow_left₀ b0 base 3).trans top) (pow_nonneg b0 _) a0).trans_eq (by
      dsimp [engineering,v]
      rw [pow_add,pow_one,pow_mul]
      ring)
  have αp:0<a^(engineering d):=pow_pos (zero_lt_one.trans_le ap) _
  have zp:0<x^(v*(j-n+1)):=pow_pos (zero_lt_one.trans_le xp) _
  have δ0:0 ≤ δ:=div_nonneg (div_nonneg (mul_nonneg (half_pos ep).le (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)) αp.le) zp.le
  refine ⟨Q1,(le_div_iff₀ (zero_lt_one.trans_le cash)).2 ?_⟩
  calc 2*δ*b^3*charge = (2*δ)*(charge*b^3):=by ring
       _ ≤ (2*δ)*(a^(engineering d)*x^(v*(j-n+1))):=mul_le_mul_of_nonneg_left invoice (by positivity)
       _ = ε*g^p:=by
         change 2*((ε/2*g^p)/a^(engineering d)/x^(v*(j-n+1)))*(a^(engineering d)*x^(v*(j-n+1)))=_
         field_simp [αp.ne',zp.ne']

end YM.Integration.WilsonAllDateHarvestFixedOriginInvoice
