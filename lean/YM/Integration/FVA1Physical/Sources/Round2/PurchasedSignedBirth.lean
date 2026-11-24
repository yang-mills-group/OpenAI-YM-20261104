import YM.Integration.FVA1Physical.Sources.Round2.SignedSeasons
import YM.Integration.FVA1Physical.Sources.Round2.SignedCost
import YM.Integration.FVA1Physical.Round2.PhysicalCurrentCharge

/-! Uniform finite-radius pricing of a genuine physical source, including
its birth on the immediately preceding measured coupling value. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Finset Lattice RG YM.Wilson Source Labels Extra.Histories Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch Roof Push.PriceCompiler
open Next.Foundations UVNext.CouplingReset Graces Roost LocalLTE LocalLTE.Vinca
open Push.Local Push.AbsoluteSums Further.LogJets Push.Uniform
open Integration.FVA1Physical.Marked RGComparison.Core16.Spool MSbar MSbar.Lis MSbar.Heath MSbar.Midpoint
open MSbar.Heath.Stock MSbar.Mosaic
open scoped Classical BigOperators Topology
variable {G:Gauge} {I:Type} [Fintype I] {d N n m:ℕ}

theorem purchased_signed_birth (R:PhysicalNext.Repeat.Legato.Run G) (hm:m<N) (start:R.t 0 ≤ m) (a:I → CoverLabel G d)
    (y:Site (R.family.side (m+1) n)) (o:I→Site (R.family.side (m+1) n)) (part:Bool) (r:ℕ)
    (placed:∀ i,separation (o i-y) 0 ≤ r) (fit:r+LocalLTE.Vault.terr G d ≤ (R.family.path.rep N n (m+1)).p.B) :
    measuredBirth R a N n m y o part r ≤ fieldShelf a (R.alloy.B.a.params (m+1)) r := by
  let H:=R.family.path
  let A:=H.rep N n (m+1)
  let h:=R.alloy.B.a.params (m+1)
  let v:=fun i=>o i-y
  let δ:=H.levels.clock.forcedAllowance (m+1)
  have hp:=R.makes.wilson.represents N n (m+1) hm
  have adv : 3 ≤ R.alloy.B.a.clock.J (m+1) := (R.makes.stages 0).1.trans
    (R.alloy.B.a.fits.mono (start.trans (Nat.le_succ _)))
  have scale:A.p=R.alloy.B.a.budget (m+1):=hp.vac
  have permit: hitWidth A.p*Real.sqrt δ ≤ 1:=by
    rw [scale,Blush.glyph_eq]
    exact R.b.stamp _ _ (step_paid R.alloy.B.a (m+1)) 0 ((Nat.zero_le 3).trans adv) _ (R.alloy.B.valid.pays (m+1))
      |>.2 _ _ (params_eq R.alloy.B.valid (m+1)) rfl
  have pay:=single_ball_fare h A.p a (by rw [scale];rfl) (by rw [scale];rfl) (by rw [scale];rfl)
    r v placed fit part (forcedPos R.alloy.B.a (m+1)) permit
  have rate:Doors.rate (H.S.block m) ≤ 1:=Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast (H.S.block m).property) (by norm_num)
  have shelf:0 ≤ fieldShelf a h r:=by
    unfold fieldShelf lampFare
    have col:0 ≤ h.columns:=zero_le_one.trans h.columns_ge
    have st:=(stencilBound_pos (freshLamps a)).le
    positivity
  exact (mul_le_mul_of_nonneg_left pay (Doors.rate_pos _).le).trans (mul_le_of_le_one_left shelf rate)

end YM.Integration.FVA1Physical.Round2.Curvature
