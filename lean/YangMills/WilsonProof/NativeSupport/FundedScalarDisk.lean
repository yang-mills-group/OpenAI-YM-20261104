import YangMills.WilsonProof.NativeSupport.FundedProjection
import YM.FullVolume.Stage.Coup

/-! A scalar slice through the actual unmarked Wilson history. The regular
and forced labels stay fixed on the incoming side. The two outgoing Taylor
majorants are uniform in the period, and their centers are the actual records. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility
open RG Wilson Lattice PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Legato.Campaign PhysicalNext.Repeat.Muse
open PhysicalNext.Repeat.Pass PhysicalNext.Repeat.Jams FullVolume.Ray
open UniformSpace AnalyticBridge.VerifiedReset Next.Scheduling
open scoped Classical
variable {G : Gauge} {R : Run G} (T : Campaign R) {N per : ℕ}

theorem scalar_tariff (a : Levels G) (m : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    Pass.fn a m v ≤ v/64 := by
  let x := a.clock.hatBeta m
  let l := Clock.gap x
  let s := a.clock.monitor m
  have hx : 1 < x := a.fits.delayed m
  have hl : 0 < l := inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  have hl₁ : l ≤ 1 := inv_le_one_of_one_le₀ (by
    change (1:ℝ) ≤ Real.sqrt x
    exact Real.one_le_sqrt.mpr hx.le)
  have hs : 1 ≤ s := Real.one_le_exp (sq_nonneg _)
  have he : δE x ≤ l^2 := by
    rw [δE, ← Real.rpow_natCast l 2]
    exact Real.rpow_le_rpow_of_exponent_ge hl hl₁ (by norm_num)
  have hmon : l^2 ≤ (l*s)^2 :=
    pow_le_pow_left₀ hl.le (le_mul_of_one_le_right hl.le hs) 2
  have hpos : 0 < (l*s)^2 := pow_pos (mul_pos hl (by linarith)) _
  change v*(Time.credit G (a.params m)*δE x)/(l*s)^2 ≤ v/64
  apply (div_le_iff₀ hpos).mpr
  have h₁ := mul_le_mul (Time.authorized G (a.params m)).1 (he.trans hmon)
    (Real.rpow_nonneg hl.le _) (by norm_num)
  exact (mul_le_mul_of_nonneg_left h₁ hv).trans_eq (by ring)

theorem scalar_disk (i : Fin N) :
    let O := halls T per N
    let p := T.center N per
    let H := T.L.prim N i per i.isLt
    let x := p.pose T.gains O i.succ
    let w : ℝ × Contest.lobby O i.succ := (1,0)
    Scout (T.width/4) (fun u : ℝ => reading H (O.walks i i.isLt) (x+u • w)) (2*T.pay) ∧
    Scout (T.width/2) (fun u : ℝ => drum H (x+u • w)) (2*Pass.fn R.alloy.B.a i T.pay) ∧
    World.ready (reading H (O.walks i i.isLt) x) =
      World.ready ((p.chair T.gains O i.castSucc : Contest.lobby O i.castSucc) :
        Completion (Contest.lobby O i.castSucc)) ∧
    drum H x =
      (R.T.history N per i).beta-(R.T.history N per (i.val+1)).beta-R.alloy.B.kin.alpha N i := by
  dsimp only
  let O := halls T per N
  let p := T.center N per
  let H := T.L.prim N i per i.isLt
  let x := p.pose T.gains O i.succ
  let w : ℝ × Contest.lobby O i.succ := (1,0)
  have climate := T.gains.largeG.scale (i.val+1)
  have band : emcee (R.alloy.B.a.clock.hatBeta (i.val+1)) x.1 :=
    Pass.samples climate (p.mildS T.gains (i.val+1) i.isLt) (sub_self x.1 ▸ (by norm_num))
  have wallet (j : sun) : ‖(x+j.val • w).2‖ ≤ 1 := by
    change ‖p.chair T.gains O i.succ+j.val • (0 : Contest.lobby O i.succ)‖ ≤ 1
    simpa only [smul_zero,add_zero] using (p.sparkN T.gains O i.succ).trans (by norm_num)
  obtain ⟨hs,hb⟩ := Pass.income T.gains.SimpleR H T.gains.Shears T.gains.Saved
    (O.walks i i.isLt) climate x w band (by norm_num [w]) wallet
  have hq := T.gains.voices.1
  have hb₂ : Rebar ((2*T.width)/2) (phraseS (fun j : sun => drum H (x+j.val • w))) (Pass.fn R.alloy.B.a i T.pay) := by
    rw [show (2*T.width)/2 = T.width by ring]
    exact hb
  have h₂ := Muse.roundTrip (q:=2*T.width) (f:=fun u : ℝ => drum H (x+u • w)) hb₂ (by linarith)
  rw [show (2*T.width)/4 = T.width/2 by ring] at h₂
  exact ⟨Muse.roundTrip (f:=fun u : ℝ => reading H (O.walks i i.isLt) (x+u • w)) hs hq,
    h₂, p.forthB T.gains O i⟩

end YM.Integration.InletSusceptibility
