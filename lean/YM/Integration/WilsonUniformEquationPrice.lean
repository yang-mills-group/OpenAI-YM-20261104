import YM.Integration.WilsonCutoffEquationRows
import YM.Integration.WilsonSignedTerminalCoordinates
import YM.Integration.WilsonMovingEquationAllowance
import YM.Integration.WilsonMovingSignedEquation

/-! A single numerical envelope before the cutoff, period and Wilson
insertion. The signed terminal inverse is inside the ultraviolet discount. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonUniformEquationPrice
open Function Set Filter MeasureTheory Lattice Wilson RG RG16 RG16.Literal Labels Source Push
open Next.Extract MergeProof PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Daisy.Charity.RG12
open Cells Extra.Histories Extra.Histories.Motion Accent
open WilsonSignedReportPrice WilsonCutoffDiscrepancyPrice
open scoped Classical Topology BigOperators
universe u
variable {G : Gauge}

private theorem combine {w t o z c e D r b : ℝ} (ht : t≤ o*z*(c*e)) (hz : z≤D*r)
    (hr : r*e≤b) (hw : 0≤w) (ho : 0≤o) (hc : 0≤c) (he : 0≤e) (hD : 0≤D) :
    w*t ≤ (o*D)*((w*c)*b) := by
  calc
    _ ≤ w*(o*z*(c*e)) := mul_le_mul_of_nonneg_left ht hw
    _ ≤ w*(o*(D*r)*(c*e)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz ho) (mul_nonneg hc he)) hw
    _ = (o*D)*((w*c)*(r*e)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr (mul_nonneg hw hc)) (mul_nonneg ho hD)

theorem issued (R : Run G) (hG : G.Simple) {T : Campaign R} (walls : Campaign.Pillars R T)
    {ε : ℝ} (props : WilsonLimitConstruction.FundedOriginalProperties.{u} hG ε walls)
    (pace : WilsonWindowReportingPace.Slow R.kit)
    {V : ∀ d, SectionData (R.family.labels.level d)} {W : Mark.Weave G}
    {P : ∀ d, (ℕ×ℕ) → (R.family.label d ≃ₗ[ℂ] R.family.label d)} {b : Presentation R.family}
    (portfolios : ∀ d, Mark.Portfolio R.family.params (V d) (W d))
    (sale : Hearthside R.family V W P b (Bandage.fly R.alloy.B.a)) (d : ℕ)
    {L B : ℝ} (hL : 0<L) (hB : 4≤B) :
    ∃ A : ℕ → ℝ, Monotone A ∧ (∀ k, 1≤A k) ∧
      (∀ δ>0, ∃ K:ℝ, 1≤K ∧ ∀ k, A k≤K*Real.exp (δ*R.family.S.scale k)) ∧
      (∀ q:ℕ, ∀ δ>0, ∀ᶠ k in atTop,
        (A (k+1)/A k)^q ≤ Real.exp (δ*(R.family.path.levels.clock.coverSize k:ℝ))) ∧
      ∀ᶠ k in atTop, ∀ N, k<N → ∀ (p : ℕ) (hm : port R.family L B hL k≤N)
      (x : R.family.label d), let y:=x-b.step d (N,p) x
      R.family.S.a k^d*(center R.family.S p hm 0).rootTest (R.family.beta N p)
        (R.family.O N p y 0-WilsonOffsetEquationLaw.incoming R.family (V d) N p (P d (N,p)) y 0)
        ≤ ‖x‖*A k := by
  let C:=R.family
  let F:=C.labels.level d
  have hb : 0<B := by linarith
  obtain ⟨E,U,stamp⟩:=sale.hearth d
  obtain ⟨a,ha⟩:=sale.uniform d
  have ha0 : 0≤a := (norm_nonneg _).trans (ha (0,0))
  let J:=WilsonSignedTerminalCoordinates.joint C E
  let D:=2*(Fintype.card F.Index:ℝ)*(1+a)
  have hD : 0≤D := mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _)) (by linarith)
  have hrot : 0≤orbitCost F := zero_le_one.trans (orbitCost_one_le _)
  let out:=WilsonMovingEquationAllowance.fare C d B hL J
  let f (_ : Unit) (k : ℕ) := (orbitCost F*D)*out k
  have he := FullVolume.borrowed (W:=E) (stamp.coined Extraction.Order.full)
  have hj := WilsonSignedTerminalCoordinates.slow C E he
  have hout := WilsonMovingEquationAllowance.funded C hG props.2.1.paid.stoves pace.2 d hL hb J hj
  obtain ⟨A,hA,pA,sub,grade⟩ := WilsonMovingEquationAllowance.alternatives C
    (Finset.univ : Finset Unit) f (fun _ _=> (FullVolume.Sluggish.const (C:=C) (orbitCost F*D)).mul hout)
    pace.2 hG
  have covers k : f () k ≤ A k := (le_abs_self _).trans (by simpa only [Finset.univ_unique,
    Finset.sum_singleton] using (pA k).2)
  obtain ⟨n,hn⟩:=eventually_atTop.mp (WilsonCutoffEquationRows.physical (V d) R.makes
    (portfolios d).valid stamp)
  obtain ⟨n',hs⟩:=eventually_atTop.mp stamp.stamped
  refine ⟨A,hA,fun k=>(pA k).1,sub,grade,?_⟩
  filter_upwards [WilsonMovingReportTreasury.opened C hG hL hB,eventually_ge_atTop n,
    eventually_ge_atTop n',eventually_ge_atTop (C.ref d),
    WilsonMovingReportFootprint.original C hG (V d).stencil hL hb,
    WilsonMovingReportFootprint.original C hG (C.localSection d).stencil hL hb] with k hO hk hk' hr fv ft
  intro N hN p hm x
  let y:=x-b.step d (N,p) x
  let z:=(P d (N,p)).symm ((C.factory d N p).terminal.symm y)
  have raw := hn N (hk.trans hN.le) p k (port C L B hL k) hr hN hO hm
    (fv N hN.le p hm 0) (ft N hN.le p hm 0) z
  have href : initial (C.localSection d) C.path N p (P d (N,p) z) 0=C.O N p y 0 := by
    rw [show P d (N,p) z = (C.factory d N p).terminal.symm y from LinearEquiv.apply_symm_apply ..]; rfl
  rw [href] at raw
  have hz := WilsonSignedTerminalCoordinates.projected C R.makes d N p (hr.trans hN.le) (P d (N,p))
    ((hs N (hk'.trans hN.le) p).2.1) (b.step d (N,p)) (ha _) x
  have ht := (WilsonSignedTerminalCoordinates.before C E k N).le.trans ((heard C J hj k).2 N)
  have hcoord : F.coeffSize z ≤ (D*‖x‖)*WilsonSignedTerminalCoordinates.column C N := hz
  have coin := combine raw hcoord ht (pow_nonneg (C.S.a_pos k).le d) hrot (conversion_pos C d _ _).le
    (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (mul_nonneg hD (norm_nonneg _))
  have renew : C.S.a k^d * conversion C d (port C L B hL k) k =
      stakes C (port C L B hL k) k*marker C d k := by
    have ha' : 0<C.S.a k^d := pow_pos (C.S.a_pos k) d
    unfold WilsonSignedReportPrice.conversion; field_simp
  rw [renew] at coin
  apply coin.trans
  calc
    _ = ‖x‖*f () k := by change _ = ‖x‖*((orbitCost F*D)*(_*_*room C J k)); ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (covers k) (norm_nonneg _)

end YM.Integration.WilsonUniformEquationPrice
