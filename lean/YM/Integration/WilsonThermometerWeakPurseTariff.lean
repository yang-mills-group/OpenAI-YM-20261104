import YM.Integration.WilsonThermometerWeakOriginalPrepared
import YM.Integration.WilsonThermometerWeakColumnWallet

/-! The original reporting purse covers each compensated displaced program up to its
published weak credit scale. The tariff permits independently displaced copies. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPurseTariff
open Function Filter Set Lattice Wilson RG Source Labels RG12 Extra.Histories
open Push.PriceCompiler RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Spindle Next.Rank Configuration Normal Rise
open Perch Glimmer LiftMark Beamer Station Atlas Tariffs MvPolynomial Ribbon Asymptotics Tapes Paint
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G)
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "B" => WilsonThermometerOffsetLedger.cash R

private theorem monotone (s:ℝ) {a b:ℝ} (h:a≤b): bill a s≤bill b s :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h (boil_pos s))

theorem paid {s f credit hw cash cap zero δ:ℝ} (D:ℕ) (hf:f+credit≤ -8) (large:2≤bill (7/8) s)
    (hw0:0≤hw) (cash0:0≤cash) (cap0:0≤cap) (unit:zero≤cap)
    (wi:hw≤bill (credit-1) s) (gross:cap+cash≤bill (1/8) s*hw)
    (fitted:δ≤bill (1/8-(D:ℝ)) s*hw):
    bill f s*cash≤bill (-8) s ∧ bill f s*(cap+zero+cash)≤3*bill (-8) s ∧
      bill f s*(δ+bill (-(D:ℝ)) s*cash)≤bill (-(D:ℝ)-8) s:=by
  have wf:0≤bill f s:=(Real.exp_pos _).le
  have price:bill f s*(cap+cash)≤bill (-8) s:=by
    apply (mul_le_mul_of_nonneg_left (gross.trans (mul_le_mul_of_nonneg_left wi (Real.exp_pos _).le)) wf).trans
    rw [←mul_assoc,overlap,overlap];apply monotone;linarith
  have sm:bill f s*cash≤bill (-8) s:=(mul_le_mul_of_nonneg_left (le_add_of_nonneg_left cap0) wf).trans price
  have bound:δ+bill (-(D:ℝ)) s*cash≤2*(bill (1/8-(D:ℝ)) s*hw):=by
    have hc:cash≤bill (1/8) s*hw:=(le_add_of_nonneg_left cap0).trans gross
    have h:=mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le (a:=bill (-(D:ℝ)) s)
    rw [←mul_assoc,overlap,show -(D:ℝ)+(1/8)=1/8-(D:ℝ) by ring] at h
    linarith only [fitted,h]
  refine ⟨sm,?_,?_⟩
  · have h:cap+zero+cash≤2*(cap+cash):=by linarith only [unit,cash0]
    apply (mul_le_mul_of_nonneg_left h wf).trans
    rw [mul_left_comm];linarith only [price,(show 0<bill (-8) s from Real.exp_pos _)]
  apply (mul_le_mul_of_nonneg_left bound wf).trans
  calc
    bill f s*(2*(bill (1/8-(D:ℝ)) s*hw)) ≤bill f s*(bill (7/8) s*(bill (1/8-(D:ℝ)) s*bill (credit-1) s)):=by
      exact mul_le_mul_of_nonneg_left (mul_le_mul large (mul_le_mul_of_nonneg_left wi (Real.exp_pos _).le)
        (mul_nonneg (Real.exp_pos _).le hw0) (Real.exp_pos _).le) wf
    _ ≤ _:=by rw [←mul_assoc,←mul_assoc,overlap,overlap,overlap];apply monotone;linarith

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (d:ℕ):
    ∀ᶠ k:ℕ in atTop,∀ N p (_:k≤N),let P:=(C).path.rep N p k;let s:=clim (A) k;let F:=(C).labels.level d
      ∀ (X:Coefficient F ((C).side k p)) (y:Palette C d) (ξ:Purse) (D:ℕ) (δ:ℝ),
      let cash:=B d k*size y;let cap:=2*((A).params k).columns*F.coeffSize X.x
      X.Format 0 (C).params P → X.remBound 0 P (kappa (C).path k) cash →
      Germ.projection F (C).params P.p.threshold 0 X=y (primaryLetter d) →
      size y≤bill (ξ.credit-1) s → δ≤bill (1/8-(D:ℝ)) s*size y →
      bill ξ.f s*cash≤bill (-8) s ∧ bill ξ.f s*(cap+‖X.x 0‖+cash)≤3*bill (-8) s ∧
        bill ξ.f s*(δ+bill (-(D:ℝ)) s*cash)≤bill (-(D:ℝ)-8) s :=by
  have large:∀ᶠ k:ℕ in atTop,(2:ℝ)≤bill (7/8) (clim (A) k):=
    ((bill_lo (by norm_num:0<(7/8:ℝ))).comp (hat_rate (A) simple)).eventually_ge_atTop 2
  filter_upwards [large,WilsonThermometerWeakColumnWallet.original R simple shop d (show 0<(1/8:ℝ) by norm_num),
    WilsonThermometerOffsetLedger.original R simple shop d] with k grow purse cash0 N p hk P s F X y ξ D δ cash cap form rem proj wallet fit
  have hx:0≤F.coeffSize X.x:=Finset.sum_nonneg fun i _=>norm_nonneg _
  have mass:0≤ size y:=size_ge _
  have hc:0≤cash:=mul_nonneg (zero_le_one.trans cash0.2.1) mass
  have base:‖X.x 0‖≤F.coeffSize X.x:=Finset.single_le_sum (fun i _=>norm_nonneg (X.x i)) (Finset.mem_univ 0)
  have ge:1≤2*((A).params k).columns:=by linarith only [((A).params k).columns_ge]
  exact paid D ξ.fits grow mass hc (mul_nonneg (zero_le_one.trans ge) hx)
    (base.trans (le_mul_of_one_le_left hx ge)) wallet (purse N p hk X y form rem proj) fit

end YM.Integration.WilsonThermometerWeakPurseTariff
end
