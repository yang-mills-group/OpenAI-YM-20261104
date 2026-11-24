import YM.Integration.WilsonMovingReportFootprint
import YM.Integration.WilsonMovingReportTreasury
import YM.Integration.WilsonSignedEquationColumns
import YM.Integration.WilsonReportCitizenRun

/-! Cutoff-to-report price of the actual projected equation discrepancy at
the RG16 moving report. Every covariance, conjugation, and sign in the
physical replication root stays in the invoice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingSignedEquation
open Function Set Filter MeasureTheory Lattice Wilson RG RG16 RG16.Literal Labels Source Push
open Next.Extract MergeProof PhysicalNext.Repeat.Legato Cells Extra.Histories Accent
open PhysicalNext.Repeat.Daisy.Charity.RG12
open WilsonSignedReportPrice WilsonCutoffDiscrepancyPrice Extra.Histories.Motion
open scoped Classical Topology BigOperators
universe u
variable {G : Gauge}

private theorem pool (C : Family G) (hG : G.Simple) (Y : OPE.Therm.Poetry C.path.levels)
    (pace : ∀ k, ((C.S.block k).val:ℝ) ≤ Real.log (Lambda C.path.levels k))
    (d : ℕ) (E : ℕ → ℝ) (hE : FullVolume.Sluggish C (fun i => E i.1))
    {L B δ : ℝ} (hL : 0<L) (hB : 0<B) (hd : 0<δ) :
    ∃ K : ℝ, 1≤K ∧ ∀ᶠ k in atTop, C.S.a k^d *
      (conversion C d (port C L B hL k) k * room C E k) ≤ K*Real.exp (δ*C.S.scale k) := by
  have hε : 0 < δ/3 := by positivity
  obtain ⟨K,hK,paid⟩ := presold C E hE hε
  refine ⟨K,hK,?_⟩
  filter_upwards [WilsonMovingReportTreasury.posted C hG Y hL hB pace hε,
    FullVolume.late.mp ((marker_paid C hG d).est hε)] with k ht hv
  let x := Real.exp ((δ/3)*C.S.scale k)
  have hm : marker C d k≤x := hv 0
  have hroom : 0 ≤ room C E k := zero_le_one.trans (heard C E hE k).1
  have ha : 0 < C.S.a k^d := pow_pos (C.S.a_pos _) _
  calc
    _ = (stakes C (port C L B hL k) k * marker C d k)*room C E k := by
      unfold conversion; field_simp
    _ ≤ (x*x)*(K*x) := mul_le_mul (mul_le_mul ht hm (marker_pos C _ _).le
      (Real.exp_pos _).le) (paid k) hroom (mul_self_nonneg x)
    _ = _ := by
      calc
        _ = K * (x * x * x) := by ring
        _ = _ := by unfold x; rw [← Real.exp_add,← Real.exp_add]; congr 2; ring

variable (R : Run G) (hG : G.Simple)
local notation "C" => R.family

/-- The projection and issuance are inputs so that this theorem joins the
one physical Ward cancellation, without selecting a different presentation. -/
theorem issued {T : Campaign R} (walls : Campaign.Pillars R T) {ε : ℝ}
    (props : WilsonLimitConstruction.FundedOriginalProperties.{u} hG ε walls)
    (pace : WilsonWindowReportingPace.Slow R.kit)
    {V : ∀ d, SectionData ((C).labels.level d)} {W : Mark.Weave G}
    {P : ∀ d, (ℕ×ℕ) → ((C).label d ≃ₗ[ℂ] (C).label d)} {b : Presentation C}
    (portfolios : ∀ d, Mark.Portfolio (C).params (V d) (W d))
    (sale : Hearthside C V W P b (Bandage.fly R.alloy.B.a)) (d : ℕ)
    {L B δ : ℝ} (hL : 0<L) (hB : 4≤B) (hd : 0<δ) :
    ∃ K : ℝ, 1≤K ∧ ∀ᶠ k in atTop, ∀ N, k<N → ∀ (p : ℕ)
    (hm : port C L B hL k≤N) (x : (C).label d),
    let y := x - b.step d (N,p) x
    (C).S.a k^d * (center (C).S p hm 0).rootTest ((C).beta N p)
        ((C).O N p y 0 - WilsonOffsetEquationLaw.incoming C (V d) N p (P d (N,p)) y 0) ≤
      (2*orbitCost ((C).labels.level d) * ((C).labels.level d).coeffSize (((C).factory d N p).terminal.symm y)) *
        (K*Real.exp (δ*(C).S.scale k)) := by
  obtain ⟨E,U,stamp⟩ := sale.hearth d
  have he := FullVolume.borrowed (W:=E) (stamp.coined Extraction.Order.full)
  have hb : 0<B := by linarith
  obtain ⟨K,hK,hpool⟩:=pool C hG props.2.1.paid.stoves pace.2 d E he hL hb hd
  obtain ⟨n,hn⟩:=eventually_atTop.mp (WilsonSignedEquationColumns.charged (V d) R.makes
    (portfolios d).valid stamp)
  obtain ⟨n',hs⟩:=eventually_atTop.mp stamp.stamped
  refine ⟨K,hK,?_⟩
  filter_upwards [hpool,WilsonMovingReportTreasury.opened C hG hL hB,eventually_ge_atTop n,
    eventually_ge_atTop n',eventually_ge_atTop ((C).ref d),
    WilsonMovingReportFootprint.original C hG (V d).stencil hL hb,
    WilsonMovingReportFootprint.original C hG ((C).localSection d).stencil hL hb] with k hc hO hk hk' hr fv ft
  intro N hN p hm x
  let y := x - b.step d (N,p) x
  let z := (P d (N,p)).symm (((C).factory d N p).terminal.symm y)
  let F := (C).labels.level d
  have prices := hn N (hk.trans hN.le) p k (port C L B hL k) hr hN hO hm
    (fv N hN.le p hm 0) (ft N hN.le p hm 0) z
  have inverse := (hs N (hk'.trans hN.le) p).2.1 (((C).factory d N p).terminal.symm y)
  have href : initial ((C).localSection d) (C).path N p (P d (N,p) z) 0 = (C).O N p y 0 := by
    rw [show P d (N,p) z = ((C).factory d N p).terminal.symm y from LinearEquiv.apply_symm_apply ..]
    rfl
  rw [href] at prices
  let cost := conversion C d (port C L B hL k) k * room C E k
  have hcoa : 0 ≤ F.coeffSize z := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hrot : 0 ≤ orbitCost F := zero_le_one.trans (orbitCost_one_le F)
  have changes : orbitCost F * F.coeffSize z ≤ 2*orbitCost F*
      F.coeffSize (((C).factory d N p).terminal.symm y) :=
    (mul_le_mul_of_nonneg_left inverse hrot).trans_eq (by ring)
  change (C).S.a k^d * (center (C).S p hm 0).rootTest ((C).beta N p) _ ≤ _
  apply (mul_le_mul_of_nonneg_left prices (pow_nonneg ((C).S.a_pos _).le _)).trans
  change (C).S.a k^d * ((orbitCost F*F.coeffSize z)*cost) ≤ _
  rw [mul_left_comm]
  exact mul_le_mul changes hc (mul_nonneg (pow_nonneg ((C).S.a_pos _).le _)
      (mul_nonneg (conversion_pos C _ _ _).le (zero_le_one.trans (heard C E he k).1)))
    ((mul_nonneg hrot hcoa).trans changes)

end YM.Integration.WilsonMovingSignedEquation
