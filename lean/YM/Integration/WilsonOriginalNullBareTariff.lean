import YM.Integration.WilsonMeasuredRankedFare
import YM.Integration.WilsonOriginalThermometerTollBudget

/-! Before both regulators, the unnormalized top invoice pays its original single hard divisor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullBareTariff
open Function Filter Finset Lattice Wilson RG Labels Source Extra.Histories Marker QuadraticLocal Ac
open Push.Local Push.AbsoluteSums Trace.Physical.Germ
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Pert.Asymptotics RG16 Push.PriceCompiler Next.Foundations
open WilsonOlderSignedOneMarkTariff
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {d:ℕ} {F:Frame G d} (S:SectionData F) (Y:Hol G)
theorem original (simple:G.Simple)
    (slow:∀ m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (ready:WilsonReportLampForecast.Ready R.family.path.levels) :
    ∀ᶠ n:ℕ in atTop, ∀ per (W:Rep G (R.family.side n per)),
    W.p=R.family.path.levels.budget n → W.p.supportExponent ≤ 100 →
    ∀ w E:ℝ, 0<w → 0 ≤ E → ∀ y:Site (R.family.side n per), ∀ cut:ℕ,
    let H:=R.alloy.B.a.clock.hatBeta (n+1)
    let B:=R.alloy.B.a.clock.hatBeta n
    let κ:=LocalComparison.forcedDivisor R.family n
    let η:=R.alloy.B.a.clock.forcedAllowance n
    let μ:=(R.family.path.levels.params n).columns
    w*WilsonOlderSignedSingletonFare.fare W.p S Y (fun _:Unit=>w) ((Stock.census Unit).fire ())
        1 {y} 0 E (κ*B^(-(cut:ℝ))) κ η μ ≤
      8*Real.exp 102*(1+2*charge Y S)*H^2*E+2*Real.exp 102 :=by
  filter_upwards [WilsonCenteredReporterClock.original R simple slow ready] with n late
  intro per W atDate strength w E wp ep y cut H B κ η μ
  obtain ⟨hx,_,move,cols,kp,_,hn,room,reserve⟩:=late (n+1) per (Nat.lt_succ_self n)
  let g:=regulatorRun R.family (n+1) per (n+1)
  have stage:WilsonCenteredLampCapture.stage W.p 0 ({()}:Finset Unit) ≤ 2*(g⁻¹)^2:=by
    rw [atDate]
    exact (WilsonCenteredCaptureGeometry.motion _ (Nat.zero_le _) _ (by simp)).trans move
  have room':hitWidth W.p*η ≤ 1:=by rw [atDate];exact room
  have reserve':hitWidth W.p*η/κ ≤ 1:=by rw [atDate];exact reserve
  have b:1 ≤ B:=(R.family.path.levels.fits.delayed n).le
  let a:=B^(-(cut:ℝ))
  have ap:0 ≤ a:=Real.rpow_nonneg (zero_le_one.trans b) _
  have al:a ≤ 1:=Real.rpow_le_one_of_one_le_of_nonpos b (by exact neg_nonpos.mpr (Nat.cast_nonneg cut))
  have paid:=WilsonOlderSignedOneMarkTariff.point (r:=1) W.p S Y (fun _:Unit=>w) () y wp zero_lt_one kp hx strength
    (zero_le_one.trans (R.family.path.levels.params n).columns_ge) cols stage hn room' reserve' ep ap
  have wages:Poly.toll (fun _:Unit=>w) ((Stock.census Unit).fire ())=w:=by simp [Poly.toll,Census.fire]
  have radius:Stoop.radius (fun _:Unit=>w) 1=(fun _:Unit=>w):=by funext x;simp [Stoop.radius]
  simp only [wages,radius,inv_one,one_mul] at paid
  let β:=(R.family.path.rep (n+1) per (n+1)).beta
  have beta:0<β:=Overlay.beta_positive R.makes.wilson le_rfl
  have sq:(g⁻¹)^2=β:=by
    change ((Real.sqrt β)⁻¹)⁻¹^2=β
    rw [inv_inv,Real.sq_sqrt beta.le]
  have upper:β ≤ 2*H:=(R.makes.wilson.represents (n+1) per (n+1) le_rfl).band.2
  have fourth:(g⁻¹)^4 ≤ 4*H^2:=by
    rw [show (g⁻¹)^4=((g⁻¹)^2)^2 by ring,sq]
    nlinarith only [sq_nonneg (2*H-β),mul_nonneg (sub_nonneg.mpr upper) (show 0≤2*H+β by linarith)]
  have wage:0 ≤ 2*Real.exp 102*(1+2*charge Y S):=by unfold charge;positivity
  rw [show κ*B^(-(cut:ℝ))=a*κ from mul_comm _ _]
  calc
    _ ≤ 2*Real.exp 102*(1+2*charge Y S)*(g⁻¹)^4*E+2*Real.exp 102*a:=paid
    _ ≤ 2*Real.exp 102*(1+2*charge Y S)*(4*H^2)*E+2*Real.exp 102*1:=
      add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left fourth wage) ep)
        (mul_le_mul_of_nonneg_left al (by positivity))
    _ = 8*Real.exp 102*(1+2*charge Y S)*H^2*E+2*Real.exp 102:=by ring
end YM.Integration.WilsonOriginalNullBareTariff
