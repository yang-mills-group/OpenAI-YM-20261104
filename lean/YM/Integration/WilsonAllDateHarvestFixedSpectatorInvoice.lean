import YM.Integration.WilsonAllDateHarvestFixedOriginInvoice
import YM.Integration.WilsonReportingTerminalMesh

/-! The true engineering and cutoff-temperature cost of a single old
spectator is purchased before all periods on the fixed-origin route. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestFixedSpectatorInvoice
open Function Filter RG Lattice Source RG05Readout RG16 PhysicalNext.Repeat.Legato
open WilsonReportHarvestReplayPhysical
open scoped Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "S" => R.family.S

def extra (m t D h:ℕ):ℝ:=((S).a m/(S).a (t+1))^D*((A).clock.hatBeta (t+1))^h

def engineering (d D:ℕ):ℕ:=WilsonAllDateHarvestFixedOriginInvoice.engineering d+(D+1)

include simple in
private theorem housed
    (slow:∀j,((S).block j).val ≤ Real.log (RG05Readout.Lambda A j)) (m D h:ℕ) :
    ∀ᶠt:ℕ in atTop, extra R m t D h ≤ ((S).a m/(S).a t)^(D+1) := by
  let q:=D+1+h
  have die:=((WilsonReportingTerminalMesh.decay R q).comp (tendsto_add_atTop_nat 1)).const_mul ((2:ℝ)^(D+1))
  rw [mul_zero] at die
  filter_upwards [die.eventually (ge_mem_nhds ((S).a_pos m))] with t mesh
  let x:=(A).clock.hatBeta (t+1)
  let z:=(A).clock.hatBeta t
  let L:ℝ:=((S).block t).val
  have old:1≤z:=((A).fits.delayed _).le
  have xp:1≤x:=((A).fits.delayed _).le
  have x0:0≤x:=zero_le_one.trans xp
  have zp:0<z:=zero_lt_one.trans_le old
  have mono:z≤x:=WilsonStartup.Timing.hat_mono A (Gauge.slopeConstant_pos simple).le t.le_succ
  have logz:=Real.log_nonneg old
  have weak:L≤Real.log (2+Real.log z):=slow t
  have bound:L≤2*x:=by
    have f:=Real.log_le_sub_one_of_pos zp
    have a:=Real.log_le_sub_one_of_pos (show 0<2+Real.log z by linarith only [logz])
    linarith only [weak,f,a,mono,xp]
  have oldMesh:(S).a t=L*(S).a (t+1):=by rw [Schedule.a_step];dsimp only [L];field_simp
  have lp:0<L:=by dsimp [L];exact_mod_cast ((S).block t).property
  have cost:(S).a t*(L^D*x^h)≤(S).a m:=calc
    _ = (S).a (t+1)*L^(D+1)*x^h:=by rw [oldMesh,pow_succ];ring
    _ ≤ (S).a (t+1)*(2*x)^(D+1)*x^h:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ lp.le bound _) ((S).a_pos _).le) (pow_nonneg x0 _)
    _ = (2:ℝ)^(D+1)*((S).a (t+1)*x^q):=by unfold q;rw [pow_add,mul_pow];ring
    _ ≤ _:=mesh
  have meshPrice:L^D*x^h≤(S).a m/(S).a t:=(le_div_iff₀ ((S).a_pos _)).2 ((mul_comm ..).trans_le cost)
  let a:=(S).a m/(S).a t
  have la:(S).a m/(S).a (t+1)=a*L:=by
    unfold a;rw [oldMesh];field_simp [lp.ne',((S).a_pos (t+1)).ne']
  unfold extra
  rw [la,mul_pow,mul_assoc,pow_succ]
  exact mul_le_mul_of_nonneg_left meshPrice (pow_nonneg (div_nonneg ((S).a_pos _).le ((S).a_pos _).le) _)

include simple in
theorem original (slow:∀j,((S).block j).val ≤ Real.log (RG05Readout.Lambda A j))
    (d H k p D h:ℕ) {ε:ℝ} (ep:0<ε) :
    ∀ᶠm:ℕ in atTop,∀n:ℕ,n ≤ m → ∀Γ:ℝ,1 ≤ Γ → ∀ᶠj:ℕ in atTop,
      m≤j ∧ m-n≤j-m ∧ n<j ∧ ∀per:ℕ,
      let N:=j+1
      let g:=(Real.sqrt ((C).path.rep N per j).beta)⁻¹
      let a:=(S).a m/(S).a j
      let Q:=allowance R m N d H
      let δ:=amount R n m j N per p (engineering d D) (WilsonReportHarvestReplayIncome.reserve 0 d H k) (ε/2)
      let price:=extra R m j D h
      1≤Q ∧ 0<price ∧ 2*δ * (WilsonAllDateHarvestIntervalPrice.bill C n j (d+1) k (Q*a))^3 ≤ ε*g^p/(Γ*price) := by
  filter_upwards [WilsonAllDateHarvestFixedOriginInvoice.original R simple d H k p ep] with m base n nm Γ cg
  filter_upwards [base n nm Γ cg,housed R simple slow m D h] with j paid done
  obtain ⟨mj,old,before,account⟩:=paid
  refine ⟨mj,old,before,?_⟩
  intro per N g a Q δ price
  have main:=account per
  let e:=WilsonAllDateHarvestFixedOriginInvoice.engineering d
  let l:=WilsonReportHarvestReplayIncome.reserve 0 d H k
  let b:=WilsonAllDateHarvestIntervalPrice.bill C n j (d+1) k (Q*a)
  let raw:=amount R n m j N per p e l (ε/2)
  have ap:0<a:=div_pos ((S).a_pos _) ((S).a_pos _)
  have xp:0<(A).clock.hatBeta j:=zero_lt_one.trans_le ((A).fits.delayed j).le
  have next:0<(A).clock.hatBeta (j+1):=zero_lt_one.trans_le ((A).fits.delayed (j+1)).le
  have vp:0<price:=mul_pos (pow_pos (div_pos ((S).a_pos _) ((S).a_pos _)) _) (pow_pos next _)
  have co:0<Γ:=zero_lt_one.trans_le cg
  have g0:0≤g:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have d0:0≤δ:=div_nonneg (div_nonneg (mul_nonneg (half_pos ep).le (pow_nonneg g0 _)) (pow_nonneg ap.le _)) (pow_nonneg xp.le _)
  have eq:δ*a^(D+1)=raw:=by
    change (((ε/2*g^p)/(a^(e+(D+1))))/(A).clock.hatBeta j^(l*(j-n+1)))*a^(D+1)=
      ((ε/2*g^p)/a^e)/(A).clock.hatBeta j^(l*(j-n+1))
    rw [pow_add];field_simp
  have spend:δ*price≤raw:=(mul_le_mul_of_nonneg_left done d0).trans_eq eq
  have account':2*raw*b^3≤ε*g^p/Γ:=main.2
  have nonneg:0≤b:=by
    change 0≤WilsonAllDateHarvestIntervalPrice.bill C n j (d+1) k (Q*a)
    exact mul_nonneg (mul_nonneg (pow_nonneg xp.le _) (mul_nonneg (zero_le_one.trans main.1) ap.le)) (pow_nonneg (div_nonneg ((S).a_pos _).le ((S).a_pos _).le) _)
  refine ⟨main.1,vp,?_⟩
  change 2*δ*b^3≤ε*g^p/(Γ*price)
  rw [←div_div,le_div_iff₀ vp]
  calc _ = 2*(δ*price)*b^3:=by ring
       _ ≤ 2*raw*b^3:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left spend (by norm_num)) (pow_nonneg nonneg _)
       _ ≤ _:=account'

end YM.Integration.WilsonAllDateHarvestFixedSpectatorInvoice
