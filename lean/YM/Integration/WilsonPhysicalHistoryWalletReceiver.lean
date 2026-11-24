import YM.Integration.WilsonPhysicalHistoryMixedCofactorCapacity
import YM.MSbar.LocalSD.Expect

/-! The real Wilson expectations of the original signed wallets are precisely
the real quadratures carried by the full complex physical conditional tower. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryWalletReceiver
open Function Filter MeasureTheory Lattice RG Wilson OPE OPE.Therm
open WilsonCoeffUV PhysicalNext.Repeat.Legato WilsonReportForwardTransfer
open scoped Classical
variable {G : Gauge}

/-- Exact identity at every held coarse field. The wallet and complex tower
use the same original physical kernel, old density and measured denominator. -/
theorem real (R : Run G) {N per j : ℕ} (live : j<N)
    (φ : Config G (R.family.side (j+1) per) → ℝ) (V : Config G (R.family.side j per)) :
    (↑(MSbar.Bulk.expect (R.family.path.levels.clock.op j per) (R.family.path.rep N per (j+1)) V φ):ℂ) =
      FVA1Physical.conditionalPush R.family.path N per j (fun U=>(φ U:ℂ)) V := by
  let S := R.family.path.levels.clock.op j per
  let P := R.family.path.rep N per (j+1)
  let μ := prior G (R.family.side (j+1) per)
  rw [WilsonPhysicalHistoryPositiveIncome.receiver R live]
  change (↑(S.push P.beta (φ*P.eval) V/S.push P.beta P.eval V):ℂ) =
    S.push P.beta (fun U=>(P.eval U:ℂ)*(φ U:ℂ)) V/((S.push P.beta P.eval V:ℝ):ℂ)
  rw [Complex.ofReal_div]
  congr 1
  change (↑(∫ U, S.density P.beta U V*(φ U*P.eval U) ∂μ):ℂ) =
    ∫ U, S.density P.beta U V • ((P.eval U:ℂ)*(φ U:ℂ)) ∂μ
  have realIntegral : (∫ U, (↑(S.density P.beta U V*(φ U*P.eval U)):ℂ) ∂μ) =
      (↑(∫ U, S.density P.beta U V*(φ U*P.eval U) ∂μ):ℂ) := integral_ofReal (𝕜:=ℂ)
  apply realIntegral.symm.trans
  apply integral_congr_ae
  exact Eventually.of_forall fun U=>by
    change (↑(S.density P.beta U V*(φ U*P.eval U)):ℂ) =
      S.density P.beta U V • ((P.eval U:ℂ)*(φ U:ℂ))
    simp only [Complex.ofReal_mul,Complex.real_smul]
    ring

theorem step (R : Run G) {N per j : ℕ} (live : j<N)
    (φ : Config G (R.family.side (j+1) per) → ℝ) :
    exterior (C:=R.family) (N:=N) j.le_succ (fun U=>(φ U:ℂ)) =
      fun V=>(↑(MSbar.Bulk.expect (R.family.path.levels.clock.op j per) (R.family.path.rep N per (j+1)) V φ):ℂ) := by
  funext V
  exact (WilsonPhysicalHistoryPositiveConditional.original R live _ V).trans (real R live φ V).symm

/-- Both physical placements are subtracted inside every normalized transfer,
with their common upstream detector and all conditioning retained. -/
theorem minus (R : Run G) {N per k t : ℕ} (kt : k ≤ t) (top : t ≤ N)
    (X Y : Config G (R.family.side t per) → ℂ)
    (hX : Integrable X (scene R.family.path N per t)) (hY : Integrable Y (scene R.family.path N per t)) :
    exterior (C:=R.family) (N:=N) kt (fun U=>X U-Y U) =
      fun V=>exterior (C:=R.family) (N:=N) kt X V-exterior (C:=R.family) (N:=N) kt Y V := by
  induction t,kt using Nat.le_induction with
  | base =>
      funext V
      unfold exterior
      rw [Push.GridApprox.pushTo_self,Push.GridApprox.pushTo_self,Push.GridApprox.pushTo_self]
      unfold weighted
      rw [mul_sub,sub_div]
  | succ t ht ih =>
      let A := exterior (C:=R.family) (N:=N) t.le_succ X
      let B := exterior (C:=R.family) (N:=N) t.le_succ Y
      have next := WilsonPhysicalHistoryPositiveTower.next_sub R top X Y hX hY
      have mid := ih (t.le_succ.trans top) A B (contract (C:=R.family) R.makes t.le_succ top _ hX).1
        (contract (C:=R.family) R.makes t.le_succ top _ hY).1
      rw [← WilsonPhysicalHistoryPositiveTower.cascade R ht t.le_succ top (fun U=>X U-Y U),next]
      rw [← WilsonPhysicalHistoryPositiveTower.cascade R ht t.le_succ top X,
        ← WilsonPhysicalHistoryPositiveTower.cascade R ht t.le_succ top Y]
      exact mid

end YM.Integration.WilsonPhysicalHistoryWalletReceiver

