import YM.Integration.WilsonRootedKioskHardWeights
import YM.Integration.WilsonCoherentMayerCourseRate
import YM.Integration.WilsonMovingMentorMarkedRate
import YM.Integration.WilsonMovingMentorHardTemperature

/-! The unshrunk regular output of the two mergers uses the full support
derivative charge of each original row. Its phase and its two real Treasury
fees are bought at one fine physical temperature. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonRootedKioskRegularRate
open Finset Filter Lattice Wilson RG Marker QuadraticLocal Ac Push Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ConnectedActivityE6 AllOrder
open scoped Classical BigOperators

theorem restored {G:Gauge} {n:Side} {V α:Type} [DecidableEq V] [Fintype V]
    {P:Rep G n} {o:V → Site n} {R:Census V} {w u:V → ℝ} {lower κ fee hard salary:ℝ}
    {model whole:α → Config G n → Poly R}
    (Z:WilsonRootedKioskSealedPost.Return P o R u lower κ fee hard model whole)
    (pos:∀j,0<w j) (small:∀j,0<u j)
    (c:R.Mode → ℝ) (positive:∀s,0 ≤ c s)
    (tolls:∀s,Poly.toll u s*c s=Poly.toll w s)
    (price:∀s,c s*fee ≤ salary):
    Z.output.E.Paid w P.p.B (P.p.supportExponent+1+1) salary := by
  obtain ⟨s,_,largest⟩:=univ.exists_max_image c ⟨R.quiet,mem_univ _⟩
  obtain ⟨f,nonneg,derivs,hit⟩:=Z.regular.budget
  refine ⟨f,nonneg,derivs,fun x=>budget_loosen (budget_mono
    (budget_scale (positive s) (hit x)) ?_ ?_) (price s)⟩
  · intro i
    split
    · exact mul_nonneg (mul_nonneg (Poly.worth pos _).le (nonneg i)) (Real.exp_pos _).le
    · exact le_rfl
  · intro i
    let r:=Z.output.E.mode i
    by_cases h:x∈Z.output.E.ground i
    · simp only [if_pos h]
      have sub:c r ≤ c s:=largest _ (mem_univ _)
      rw [←tolls]
      exact (by
        calc
          _ = c r*(Poly.toll u r*f i*Real.exp _) :=by ring
          _ ≤ _:=mul_le_mul_of_nonneg_right sub
            (mul_nonneg (mul_nonneg (Poly.worth small _).le (nonneg i)) (Real.exp_pos _).le))
    · simp [h]

theorem salary {G:Gauge} (R:Run G) (simple:G.Simple) (p grade k:ℕ)
    (deep:p+5 ≤ grade) (old:p+2 ≤ 3*k+2):
    ∀ᶠ m:ℕ in atTop,∀ N per,m<N → ∀ Ω:ℝ,0 ≤ Ω →
      Ω ≤ R.alloy.B.a.clock.hatBeta (m+1)^(Beaming.grain (R.alloy.B.a.clock.J m)) →
      let g:=Coat.gStep (R.family.path.rep N per (m+1)).beta
      ∃ e:ℝ,0<e ∧ e ≤ 1 ∧
        8*Ω*(e+Burn.young (R.alloy.B.a.clock.hatBeta (m+1)) k+
          (Pressure.betaF G (R.alloy.B.a.clock.hatBeta m) (R.rolls.L (R.alloy.B.a.clock.J (m+1))))^
            Mentor.Tuition.need grade (Mentor.Tolerance (R.alloy.B.a.clock.J m))) ≤ g^p := by
  have cap:Burn.credit k=WilsonMovingMentorMarkedRate.exponent k:=by
    norm_num [Burn.credit,Burn.alt,Burn.extraN,WilsonMovingMentorMarkedRate.exponent]
    ring
  filter_upwards [WilsonCoherentMayerCourseRate.purchased R simple (p+2) (show (0:ℝ)<1/48 by norm_num),
    WilsonMovingMentorMarkedRate.original R simple (p+2) k old (show (0:ℝ)<1/48 by norm_num)]
    with m rent invoice
  intro N per live Ω omega0 ceiling g
  let x:=R.alloy.B.a.clock.hatBeta (m+1)
  let β:=(R.family.path.rep N per (m+1)).beta
  let a:=(1/48:ℝ)*g^(p+2)
  let e:=min 1 a
  have one:1 ≤ x:=(R.alloy.B.a.fits.delayed (m+1)).le
  have lo: x/2 ≤ β:=(R.makes.wilson.represents N per (m+1) (Nat.succ_le_of_lt live)).band.1
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (by linarith only [lo,one]))
  have ap:0<a:=mul_pos (by norm_num) (pow_pos gp _)
  have up:Ω ≤ x:=ceiling.trans ((Real.rpow_le_rpow_of_exponent_le one (show Beaming.grain _ ≤ 1 from by
    unfold Beaming.grain;rw [one_div];exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)))).trans_eq (Real.rpow_one _))
  have temp:g^2*x ≤ 2:=by
    simpa only [zero_add,pow_zero,pow_one,one_mul,mul_one] using
      WilsonMovingMentorHardTemperature.measured R (Nat.succ_le_of_lt live) per 1 0
  have reserve:g^2*Ω ≤ 2:=(mul_le_mul_of_nonneg_left up (sq_nonneg g)).trans temp
  have past:Burn.young x k ≤ a:=by
    simpa only [Burn.young,cap,a,g,x,Pert.Asymptotics.regulatorRun,Coat.gStep] using
      invoice N per (m+1) (Nat.le_succ _) (Nat.succ_le_of_lt live)
  have new:=rent grade (by omega) N per live
  refine ⟨e,lt_min zero_lt_one ap,min_le_left _ _,?_⟩
  calc
    _ ≤ 8*Ω*(a+a+a):=mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (min_le_right _ _) past) new) (by positivity)
    _ = g^p*((8*3/48)*(g^2*Ω)):=by dsimp only [a]; rw [pow_add];ring
    _ ≤ g^p*1:=mul_le_mul_of_nonneg_left (by nlinarith only [reserve]) (pow_nonneg gp.le _)
    _ = _:=mul_one _

end YM.Integration.WilsonRootedKioskRegularRate
