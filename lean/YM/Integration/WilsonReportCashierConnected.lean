import YM.Integration.WilsonReportCashierWindow
import YM.Integration.WilsonReportCashierPrice
import YM.Integration.WilsonReportPartialCumulant
import YM.Integration.WilsonReportSeparatedMoments
import YM.Integration.WilsonReportCitizenRun

/-! Genuinely regulated connected vacuum Wilson correlations at every fine
site of the submitted RG17 vacuum test. The ordered physical product uses
all its signed Möbius terms; the fine-site offset stays in the same law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportCashierConnected
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction
open Next.Rank Next.Rank.Spindle OPE OPE.Yarn OPE.Strobe OPE.Strobe.Vista26
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Daisy.Charity.RG12 WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open Table OPE.Orbits RG12 RG17 WilsonReportFineSmear WilsonReportMomentDifference
open Extra.Trajectories (connected)
open scoped Topology BigOperators Classical
universe u
variable {G : Gauge} {C : Family G} {n N p k : ℕ}

/-- Original finest-site regulator cumulant in the signed connected convention. -/
def observed (Γ : Census (Fin n)) (d : Fin n→ℕ) (v : (j:Fin n)→C.label (d j))
    (y : Fin n→Site (C.side N p)) (s : Γ.Mode) : ℂ :=
  (connected (microscopic Γ C (fun j => C.O N p (v j) (y j)))).part s

/-- The unaltered finite Wilson fine-site minus real parent-anchor correction,
including all of its disconnected algebra. -/
def displaced (Γ : Census (Fin n)) (hk : k≤N) (d : Fin n→ℕ) (v : (j:Fin n)→C.label (d j))
    (y : Fin n→Site (C.side N p)) (s : Γ.Mode) : ℂ :=
  observed Γ d v y s -
   (connected (microscopic Γ C (BarePack d (fun j => (C.S.toDepth hk p).parent (y j)) hk v))).part s

private theorem purchase (hG : G.Simple) (hC : C.Makes) (q : ℕ) {c ε : ℝ} (hc : 0≤c) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop,∀ N p,k≤N →
    c*Pert.Asymptotics.regulatorRun C N p k^(2*(q+1))≤ε*Pert.Asymptotics.regulatorRun C N p k^q := by
  have hc1 : 0<c+1 := by linarith only [hc]
  let a := min 1 (ε/(c+1))
  have ha : 0<a := lt_min zero_lt_one (div_pos hε hc1)
  filter_upwards [(Station.hat_rate C.path.levels hG).eventually_ge_atTop (2*a⁻¹^2)] with k large N p hk
  let b := C.path.β N p k
  let g := Pert.Asymptotics.regulatorRun C N p k
  have lower : C.path.levels.clock.hatBeta k/2≤b := (hC.wilson.represents N p k hk).band.1
  have square : a⁻¹^2≤b := by linarith only [large,lower]
  have hb := (sq_pos_of_pos (inv_pos.mpr ha)).trans_le square
  have inv := (Real.le_sqrt (inv_nonneg.mpr ha.le) hb.le).mpr square
  have gp : 0<g := inv_pos.mpr (Real.sqrt_pos.mpr hb)
  have small : g≤a := by
    change (Real.sqrt b)⁻¹≤a
    simpa only [one_div,inv_inv] using one_div_le_one_div_of_le (inv_pos.mpr ha) inv
  have g1 : g≤1 := small.trans (min_le_left ..)
  have power : g^(q+2)≤a := by
    rw [pow_succ]
    exact (mul_le_of_le_one_left gp.le (pow_le_one₀ gp.le g1)).trans small
  have paid : c*a≤ε := by
    have eq := (le_div_iff₀ hc1).mp (min_le_right 1 (ε/(c+1)))
    change a*(c+1)≤ε at eq
    nlinarith only [eq,ha.le]
  change c*g^(2*(q+1))≤ε*g^q
  rw [show 2*(q+1)=(q+2)+q by omega,pow_add,←mul_assoc]
  exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left power hc).trans paid) (pow_nonneg gp.le _)

/-- On the same funded run and the original regulated RG17 vacuum test,
remove every early mixed term at arbitrary order, with finitely many marks.
The result covers the whole regular field as well as any per-cell choice of
which finite labels have already reported to their common coarse field. -/
theorem on_run {R : Run G} (hG : G.Simple) {U : Campaign R} (W : Campaign.Pillars R U)
    {δ : ℝ} (original : FundedOriginalProperties.{u} hG δ W)
    (subsidy : WilsonReportColumnSubsidy.Eligible R.kit) (pace : WilsonWindowReportingPace.Slow R.kit)
    {S : Table R.family.book} {f : Extraction.Order} {F : Spec.Final R.family f S}
    (loc : Layout F) (T : Test 1) {n : ℕ} (Γ : Census (Fin (n+1))) (d : Fin (n+1)→ℕ)
    (t q : ℕ) {ε : ℝ} (hε : 0<ε) {K : Set (Points (n+1))} (hK : IsCompact K)
    (hc : K⊆conf _) (B : ℕ) (big : 17≤B) :
    ∀ᶠ r in RG17.home,let C := R.family
    let k := WilsonMeasuredWindow.stop C.path.levels hG B r
    ∀ N p,∀ hk : k<N,∀ v : (j:Fin (n+1))→C.label (d j),
    let V := fun j => RG17.atRef loc (d j) r (N,p) (v j)
    (∀ j,Spindle.paid C (d j) k N p (V j)≤C.path.levels.clock.hatBeta k^t) →
    ∀ ψ : Test (n+1),tsupport ψ⊆K → ∀ b : ℝ,Demand 0 ψ b →
    let Y := Fin (n+1)→Site (C.side N p)
    let w := weight C (RG17.shape (RG17.cashier F T) r ψ)
    let A (y : Y) (s : Γ.Mode) := observed Γ d V y s-displaced Γ hk.le d V y s
    let x (y : Y) (j : Fin (n+1)) := (C.S.toDepth hk.le p).parent (y j)
    let error := ε*b*Pert.Asymptotics.regulatorRun C N p k^q
    ∀ s : Γ.Mode,∀ M : Y→Finset (Fin (n+1)),
    ‖∑ y : Y,w y*(A y s-(connected (WilsonReportPartialCumulant.scheduled Γ (M y) hk.le d (x y) V)).part s)‖ ≤ error ∧
    ‖∑ y : Y,w y*(A y s-(connected (reported Γ C (N:=N) (regularPack (N:=N) d (x y) V))).part s)‖ ≤ error := by
  let C := R.family
  let stop := WilsonMeasuredWindow.stop C.path.levels hG B
  obtain ⟨citizen,book⟩ := WilsonReportCitizenRun.on_run hG W original subsidy
  obtain ⟨br,hbr,grid⟩ := WilsonReportCashierWindow.admitted hG pace F T hK hc B big
  obtain ⟨a,ha,price⟩ := WilsonReportCashierPrice.purchased F T hK hc
  let P (s : Γ.Mode) := 2*multiplicity Γ s*2^(q+1)
  let Z (s : Γ.Mode) := WilsonReportSeparatedMoments.fee Γ s (q+1)
  let C₀ := ∑ s : Γ.Mode,(P s+Z s)
  have posP (s) : 0≤P s := mul_nonneg (mul_nonneg (by norm_num) (WilsonReportSeparatedMoments.count_nonneg Γ s)) (by positivity)
  have posZ (s) : 0≤Z s := WilsonReportSeparatedMoments.fee_nonneg Γ s (q+1)
  have cn : 0≤C₀ := sum_nonneg fun s _ => add_nonneg (posP s) (posZ s)
  have fees (s) : P s≤C₀ ∧ Z s≤C₀ := by
    have total : P s+Z s≤C₀ := single_le_sum (fun i _ => add_nonneg (posP i) (posZ i)) (mem_univ s)
    exact ⟨(le_add_of_nonneg_right (posZ s)).trans total,(le_add_of_nonneg_left (posP s)).trans total⟩
  have p := WilsonReportPartialCumulant.purchased hG R.makes book.money citizen Γ d hbr t (q+1)
  have z := WilsonReportSeparatedMoments.purchased hG R.makes book.money citizen Γ d hbr 1 t (q+1)
  obtain ⟨grow,band⟩ := WilsonFundedMeasuredWindow.all_radii R pace hG (B:=B) (by omega)
  filter_upwards [grid,price,grow.eventually p,grow.eventually z,grow.eventually (purchase hG R.makes q (mul_nonneg ha cn) hε),
    RG17.positiveLength,(eventually_le_nhds (C.S.a_pos 0)).filter_mono nhdsWithin_le_nhds] with r sites weights partialResult fullResult gain pos small
  let k := stop r
  have gate := (band r pos small).1
  have lit : 1≤RG16.Lambda C.path.levels k := by
    change 1≤2+Real.log _; linarith only [Real.log_nonneg (C.path.levels.fits.delayed k).le]
  have ak : C.S.a k≤r := by
    have pn := (le_div_iff₀ (C.S.a_pos k)).mp ((one_le_pow₀ lit (n:=B)).trans gate)
    simpa only [one_mul] using pn
  obtain ⟨dis,low,up,active⟩ := sites
  have cap : (dis:ℝ)≤C.path.levels.clock.hatBeta k^1 := by rw [pow_one]; exact up
  dsimp only
  intro N period hk v tariff ψ inside b fixed s M
  let V := fun j => RG17.atRef loc (d j) r (N,period) (v j)
  let g := Pert.Asymptotics.regulatorRun C N period k
  let op := RG17.shape (RG17.cashier F T) r ψ
  let Y := Fin (n+1)→Site (C.side N period)
  let w (y : Y) := weight C op y
  let x (y : Y) (j : Fin (n+1)) := (C.S.toDepth hk.le period).parent (y j)
  let anchored (y : Y) := (connected (microscopic Γ C (BarePack d (x y) hk.le V))).part s
  let emitted (y : Y) := (connected (WilsonReportPartialCumulant.scheduled Γ (M y) hk.le d (x y) V)).part s
  let whole (y : Y) := (connected (reported Γ C (N:=N) (regularPack (N:=N) d (x y) V))).part s
  let q' := 2*(q+1)
  have power : 0≤g^q' := by dsimp only [q']; rw [pow_mul]; positivity
  have money := weights ψ inside b fixed k N period hk.le ((C.S.strictAnti.antitone hk.le).trans ak)
  change (∑ y,‖w y‖) ≤ a*b at money
  have raw (y : Y) : observed Γ d V y s-displaced Γ hk.le d V y s=anchored y := by
    unfold displaced; abel
  have each (y : Y) (live : op (Order.cells C N period y)≠0) :
      ‖anchored y-emitted y‖≤C₀*g^q' ∧ ‖anchored y-whole y‖≤C₀*g^q' := by
    have joined := active N period hk.le y
      (RG17.gathered C F T K hK inside (subset_tsupport op live))
    exact ⟨(partialResult dis low up N period hk (x y) joined V tariff (M y) s).trans
      (mul_le_mul_of_nonneg_right (fees s).1 power),
      (fullResult dis low cap N period hk (x y) joined V tariff s).trans
      (mul_le_mul_of_nonneg_right (fees s).2 power)⟩
  have sumBill (value : Y→ℂ) (valid : ∀ y,op (Order.cells C N period y)≠0 → ‖anchored y-value y‖≤C₀*g^q') :
      ‖∑ y,w y*(observed Γ d V y s-displaced Γ hk.le d V y s-value y)‖ ≤ ε*b*g^q := by
    have result : ‖∑ y,w y*(observed Γ d V y s-displaced Γ hk.le d V y s-value y)‖ ≤ (∑ y,‖w y‖)*(C₀*g^q') := by
      rw [sum_mul]
      refine (norm_sum_le ..).trans (sum_le_sum (fun y _ => ?_))
      by_cases hit : op (Order.cells C N period y)=0
      · simp [w,WilsonReportFineSmear.weight,hit]
      · rw [norm_mul,raw]; exact mul_le_mul_of_nonneg_left (valid y hit) (norm_nonneg _)
    calc
      _ ≤ (a*b)*(C₀*g^q') := result.trans (mul_le_mul_of_nonneg_right money (mul_nonneg cn power))
      _ = ((a*C₀)*g^q')*b := by ring
      _ ≤ (ε*g^q)*b := mul_le_mul_of_nonneg_right (gain N period hk.le) fixed.nonneg
      _ = _ := by ring
  exact ⟨sumBill emitted (fun y hy => (each y hy).1),sumBill whole (fun y hy => (each y hy).2)⟩

end YM.Integration.WilsonReportCashierConnected
end

