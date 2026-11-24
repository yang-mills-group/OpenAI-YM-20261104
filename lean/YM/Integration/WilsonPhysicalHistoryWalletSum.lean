import YM.Integration.WilsonPhysicalHistoryWalletSignedPair

/-! Finite complex superposition of the actual physical normalized posterior.
No factor belonging to the terminal coefficient is discarded. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryWalletSum
open Function Filter Finset MeasureTheory Lattice RG Wilson OPE OPE.Therm
open WilsonCoeffUV PhysicalNext.Repeat.Legato WilsonReportForwardTransfer
open scoped BigOperators Classical
variable {G : Gauge}

private theorem scaledStep (R : Run G) {N per j : ℕ} (live : j<N) (c : ℂ)
    (X : Config G (R.family.side (j+1) per)→ℂ) :
    exterior (C:=R.family) (N:=N) j.le_succ (fun U=>c*X U) =
      fun V=>c*exterior (C:=R.family) (N:=N) j.le_succ X V := by
  let S:=R.family.path.levels.clock.op j per
  let P:=R.family.path.rep N per (j+1)
  funext V
  rw [WilsonPhysicalHistoryPositiveConditional.original R live (fun U=>c*X U) V,
    WilsonPhysicalHistoryPositiveConditional.original R live X V,
    WilsonPhysicalHistoryPositiveIncome.receiver R live (fun U=>c*X U) V,
    WilsonPhysicalHistoryPositiveIncome.receiver R live X V]
  have same : S.push P.beta (fun U=>(P.eval U:ℂ)*(c*X U)) V =
      c*S.push P.beta (fun U=>(P.eval U:ℂ)*X U) V := by
    unfold StepData.push
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun U=>by
      change S.density P.beta U V • ((P.eval U:ℂ)*(c*X U)) =
        c*(S.density P.beta U V • ((P.eval U:ℂ)*X U))
      simp only [Complex.real_smul]
      ring
  change S.push P.beta (fun U=>(P.eval U:ℂ)*(c*X U)) V/(↑(S.push P.beta P.eval V):ℂ) =
    c*(S.push P.beta (fun U=>(P.eval U:ℂ)*X U) V/(↑(S.push P.beta P.eval V):ℂ))
  rw [same]
  ring

theorem scaled (R : Run G) {N per k t : ℕ} (kt : k≤t) (top : t≤N) (c : ℂ)
    (X : Config G (R.family.side t per)→ℂ) :
    exterior (C:=R.family) (N:=N) kt (fun U=>c*X U) =
      fun V=>c*exterior (C:=R.family) (N:=N) kt X V := by
  induction t,kt using Nat.le_induction with
  | base =>
      funext V
      unfold exterior
      rw [Push.GridApprox.pushTo_self,Push.GridApprox.pushTo_self]
      unfold weighted
      ring
  | succ t ht ih =>
      rw [← WilsonPhysicalHistoryPositiveTower.cascade R ht t.le_succ top (fun U=>c*X U),scaledStep R top,
        ← WilsonPhysicalHistoryPositiveTower.cascade R ht t.le_succ top X]
      exact ih (t.le_succ.trans top) _

theorem added (R : Run G) {N per k t : ℕ} (kt : k≤t) (top : t≤N)
    (X Y : Config G (R.family.side t per)→ℂ)
    (hX : Integrable X (scene R.family.path N per t)) (hY : Integrable Y (scene R.family.path N per t)) :
    exterior (C:=R.family) (N:=N) kt (fun U=>X U+Y U) =
      fun V=>exterior (C:=R.family) (N:=N) kt X V+exterior (C:=R.family) (N:=N) kt Y V := by
  have source : (fun U=>X U+Y U) = (fun U=>X U-(-1:ℂ)*Y U) := by funext U;ring
  rw [source,WilsonPhysicalHistoryWalletReceiver.minus R kt top X _ hX (hY.const_mul (-1)),
    scaled R kt top (-1) Y]
  funext V
  ring

theorem full (R : Run G) {N per k t : ℕ} (kt : k≤t) (top : t≤N)
    {I : Type} (s : Finset I) (F : I → Config G (R.family.side t per) → ℂ)
    (hF : ∀i, Integrable (F i) (scene R.family.path N per t)) :
    exterior (C:=R.family) (N:=N) kt (fun U=>∑i∈s,F i U) =
      fun V=>∑i∈s,exterior (C:=R.family) (N:=N) kt (F i) V := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [sum_empty,zero_mul] using scaled R kt top 0 (fun _=>(0:ℂ))
  | @insert i s hi ih =>
      simp only [sum_insert hi]
      rw [added R kt top _ _ (hF i) (integrable_finsetSum _ fun j _=>hF j),ih]

end YM.Integration.WilsonPhysicalHistoryWalletSum

