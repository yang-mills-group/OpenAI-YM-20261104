import YM.Integration.WilsonLimitConstruction.FundedFormalEconomy
import YM.FVA2.ScaleGenerator

/-! Finite formal changes between the two real coupling conventions, evaluated
on the exact physical panel and the original moving regulator target. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFormalCouplingTransition

open Lattice Labels PhysicalNext.Repeat.Legato FVA2 FVA2.Verne
open MS MS.Local.Physical MS.Menus MS.Land FVA2.ColorCode FVA2.ArchTurn
open RegulatorIR.FVAAlt2.Moving FormalOPE.RG10.Carryon
open NativeFormalSharedCoupling NativeFormalPrescriptionAgreement
open WilsonLimitConstruction.FundedFormalEconomy
open PowerSeries

variable {G : Gauge} {F : Frames G}

def physical (p : Hop F) : Warp :=
  ⟨PowerSeries.mk p.f, by rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]; exact p.rooted⟩

theorem physical_primary (p : Hop F) : coeff 1 (physical p).x = 1 := by
  change coeff 1 (PowerSeries.mk p.f) = 1
  rw [coeff_mk, p.primary]

/-- Each FVA2 scalar-jet substitution is the corresponding series substitution. -/
theorem jet (p : Hop F) (v : ℕ → ℝ) :
    mk (PositionX.Jet.ren p.f v) = (physical p).charge (mk v) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_mk, RadScale.substitute _ p.rooted, Warp.turning,
    PertExtension.Position.AlignSeries.subst_finite (physical p).atOrigin]
  simp only [coeff_mk, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm ..

/-- Writing a quantity already expressed in b in the coordinates of a. -/
def change (a b : Warp) := a.step b.refund

theorem exchange (a b : Warp) (hb : b.Hot) (u : PowerSeries ℝ) :
    (change a b).charge (b.charge u) = a.charge u := by
  calc
    _ = a.charge (b.refund.charge (b.charge u)) := Warp.take ..
    _ = a.charge ((b.refund.step b).charge u) := congrArg a.charge (Warp.take b.refund b u).symm
    _ = _ := by rw [b.cash hb, Warp.still_charge]

theorem roundtrip (a b : Warp) (ha : a.Hot) (hb : b.Hot) (u : PowerSeries ℝ) :
    (change b a).charge ((change a b).charge u) = u := by
  change (change b a).charge ((a.step b.refund).charge u) = u
  rw [Warp.take a b.refund, exchange b a ha, ← Warp.take b b.refund, b.deposit hb, Warp.still_charge]

/-- Order n uses only the first n+1 coefficients of the input. -/
theorem finite (a : Warp) {n : ℕ} {u v : PowerSeries ℝ}
    (h : ∀ j ≤ n, coeff j u = coeff j v) : coeff n (a.charge u) = coeff n (a.charge v) := by
  rw [Warp.turning, Warp.turning, PertExtension.Position.AlignSeries.subst_finite a.atOrigin,
    PertExtension.Position.AlignSeries.subst_finite a.atOrigin]
  exact Finset.sum_congr rfl fun j hj => congrArg (fun q => q * coeff n (a.x ^ j))
    (h j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))

theorem refund_primary (a : Warp) (h : coeff 1 a.x = 1) : coeff 1 a.refund.x = 1 := by
  have ha : a.Hot := h.trans_ne one_ne_zero
  have he := congrArg (fun w : Warp => coeff 1 w.x) (a.cash ha)
  change coeff 1 (a.refund.charge a.x) = coeff 1 (X : PowerSeries ℝ) at he
  simpa only [Warp.heats, h, one_mul, coeff_one_X] using he

theorem change_primary (a b : Warp) (ha : coeff 1 a.x = 1) (hb : coeff 1 b.x = 1) :
    coeff 1 (change a b).x = 1 := by
  change coeff 1 (a.charge b.refund.x) = 1
  rw [Warp.heats, refund_primary b hb, ha, one_mul]

private theorem moving_primary (R : Run G) {D : Deck G} (e : nativeDeck R = D)
    {A : Booked D} {M : MS_Data G A} {P : Prescription D} (h : MovingOn R e A M P) (μ : ℝ) :
    coeff 1 (Convention (Init (YM.FVAAlt2.Home.Report.science μ M R.family.labels) (Study.Plan R).stock)).x = 1 := by
  subst D
  obtain ⟨_, _, hm⟩ := h
  exact (hm.apply_M μ).hot

variable {R : Run G} {hG : G.Simple}

theorem purchased_primary (W : Bank R hG) (μ : ℝ) : coeff 1 (W.convention μ).x = 1 := by
  obtain ⟨_, _, _, _, _, _, _, h⟩ := W.accepted
  unfold Bank.convention
  rw [← NativeFormalDetectorReadings.report R hG rfl W.data μ]
  exact moving_primary R (NativeFormalDeckAgreement.moving_deck R) h μ

def transition (W : Bank R hG) (μ : ℝ) (p : Hop R.family.labels) :=
  change (W.convention μ).refund (physical p)

theorem tangent (W : Bank R hG) (μ : ℝ) (p : Hop R.family.labels) :
    coeff 1 (transition W μ p).x = 1 :=
  change_primary _ _ (refund_primary _ (purchased_primary W μ)) (physical_primary p)

/-- On the same bank, recalibration of the FVA2-coupling reading, followed
by the purchased moving field matrix, yields the original regulator target. -/
def Transfers (W : Bank R hG) (μ : ℝ) (p : Hop R.family.labels) : Prop :=
  ∀ d : ℕ, ∀ v : YM.FVAAlt2.Home.Datum (FormalOPE.RG10.Position.Deck R.family.labels d),
    YM.FVAAlt2.Home.mix ((transition W μ p).charge ∘ (physical p).charge ∘
        NativeFormalDetectorReadings.panel R rfl W.data μ d)
      (FormalOPE.RG10.Position.Grade.tile (FormalOPE.RG10.Position.Deck.price R.family.labels d) (W.field μ d)) v =
    YM.FVAAlt2.Home.mix ((YM.FVAAlt2.Convert.f (Study.Plan R) μ W.native.2).charge ∘
      YM.FVAAlt2.Home.Report.science μ W.native.2 R.family.labels d)
      (YM.FVAAlt2.Mass.ζfinal (Study.Plan R) μ W.native.2 d) v

theorem target (W : Bank R hG) (μ : ℝ) (p : Hop R.family.labels) : Transfers W μ p := by
  intro d v
  rw [W.target]
  apply congrArg (fun f => YM.FVAAlt2.Home.mix f
    (FormalOPE.RG10.Position.Grade.tile (FormalOPE.RG10.Position.Deck.price R.family.labels d) (W.field μ d)) v)
  exact funext fun z => exchange _ (physical p) ((physical_primary p).trans_ne one_ne_zero)
    (NativeFormalDetectorReadings.panel R rfl W.data μ d z)

/-- The relative coordinate applies to the actual transfer exposed by the
original funded FVA2 Economy. -/
theorem paid (W : Bank R hG) (μ : ℝ) :
    let V := warehouse R
    ∃ (P : Prescription (wings G)) (S : Blaze.ExactSpin V P) (U : Frost.Trusted P)
      (k : ℝ) (J : PositionX.Bend.Booth k V.F) (X : Pic.pass V hG W.data J),
      Atoll.Main.Economy hG V W.book W.data P S U J ∧
      MovingOn R (NativeFormalDeckAgreement.moving_deck R) (angular W.book V) W.data P ∧
      Transfers W μ (Forge.transfer V W.data J μ X) := by
  obtain ⟨P, S, U, k, J, _, H, h⟩ := W.accepted
  obtain ⟨X, _⟩ := H.hymns μ
  exact ⟨P, S, U, k, J, X, H, h, target W μ _⟩

end YM.Integration.NativeFormalCouplingTransition
end
