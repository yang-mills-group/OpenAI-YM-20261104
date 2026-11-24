import YM.Integration.WilsonPhysicalHistoryWalletBirthShelf

/-! One lawful extra numerical invoice for the original existence run. It
pays every fixed signed axial step and the entire range of authentic fitting
birth radii, with no count of RG steps in the perturbative-order reserve. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryWalletPurchase
open Function Filter Finset RG Precision RG.Supply Input Org PhysicalNext PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato Push.PriceCompiler Next.Foundations
open FVA1Physical.Wilson FVA1Physical.Round2.Curvature MSbar MSbar.Heath MSbar.Mosaic Pressure
open WilsonConditionalTaylorThreshold WilsonConditionalTaylorCalendar WilsonConditionalTaylorLabels
open WilsonLimitConstruction.FundedCompanySelection
open scoped Classical Topology
variable {G : Gauge}
variable (V : Voice G) (cle : Clear G V) (simple : G.Simple)

abbrev Axis := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
abbrev Request (G : Gauge) := (Entry G × ℕ) ⊕ Axis

def fare (r : Request G) (_ : MapPrices) : Fare :=
  match r with
  | .inl (α,h) => fun H _ _ _=>(eventually_atTop.mp
      (WilsonPhysicalHistoryWalletBirthShelf.all_radii (WilsonPhysicalHistoryWalletExperiment.cover α.1 α.2)
        H (loss_pos h))).choose
  | .inr (p,m,s,D,q,e) => fun H H' P K=>
      if br:P.Branches K G then WilsonPhysicalHistoryWalletAxialPacket.cutoff V cle simple H H' P K br
        p m s (Nat.cast_nonneg D) (-(q:ℝ)) (e:ℝ) else 0

def dues := @Paid G (atlas (fare V cle simple))

theorem prepaid (s : Sheet G) (M : MapPrices) : WilsonFundedWindowMenu.Prepared (@dues G V cle simple) s M :=
  WilsonConditionalTaylorThreshold.prepaid _ s M

theorem shelf (R : Run G) (fund : dues V cle simple R.kit) (α : Entry G) (h : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ r≤radiusB (R.family.path.levels.clock.hatBeta j),
      fieldShelf (WilsonPhysicalHistoryWalletExperiment.cover α.1 α.2) (R.family.path.levels.params j) r ≤
      (R.family.path.levels.clock.hatBeta j)^(loss h) := by
  filter_upwards [WilsonConditionalTaylorCalendar.read R (fare V cle simple) fund (.inl (α,h))] with j site
  exact (eventually_atTop.mp (WilsonPhysicalHistoryWalletBirthShelf.all_radii
      (WilsonPhysicalHistoryWalletExperiment.cover α.1 α.2) (R.family.path.levels.params j) (loss_pos h))).choose_spec
    (R.family.path.levels.clock.hatBeta j) (site 0)

theorem gate (R : Run G) (fund : dues V cle simple R.kit) (p m s D q e : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ per : ℕ,
      let H:=R.family.path.levels
      let S:=H.clock.op j per
      WilsonPhysicalHistoryWalletAxialPacket.cutoff V cle simple (H.params j) (H.params (j+1)) S.patch S.kernel
        (H.blocks j per).branches p m s (Nat.cast_nonneg D) (-(q:ℝ)) (e:ℝ) ≤ H.clock.hatBeta j := by
  filter_upwards [WilsonConditionalTaylorCalendar.read R (fare V cle simple) fund (.inr (p,m,s,D,q,e))] with j site per
  let H:=R.family.path.levels
  let S:=H.clock.op j per
  have br : S.patch.Branches S.kernel G := (H.blocks j per).branches
  have paid := site per
  change (if w:S.patch.Branches S.kernel G then WilsonPhysicalHistoryWalletAxialPacket.cutoff V cle simple
    (H.params j) (H.params (j+1)) S.patch S.kernel w p m s (Nat.cast_nonneg D) (-(q:ℝ)) (e:ℝ) else 0) ≤ H.clock.hatBeta j at paid
  rw [dif_pos br] at paid
  exact paid

end YM.Integration.WilsonPhysicalHistoryWalletPurchase

