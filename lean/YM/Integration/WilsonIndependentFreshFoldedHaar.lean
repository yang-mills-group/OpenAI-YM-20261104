import YM.Integration.WilsonIndependentFreshFiniteWage
import YM.Integration.WilsonIndependentFiniteHaar

/-! The actual finite Gaussian and Haar scalar minus the final cover scalar
of the same marked history. Its fare includes winding in capture units. -/
noncomputable section
namespace YM.Integration.WilsonIndependentFreshFoldedHaar
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open Budget Budget.Packet Budget.Tariff Budget.Layer Budget.Tuple Budget.Deck Uniform Uniform.Post Function Step Diagram Gradient Spatial
open scoped ENNReal Classical
variable {W : Type} {M : W → ℕ} {X Y : Page M → Type} (S : Sky X Y)
  (T : S.Accounts) {m : ℕ} (Z : T.Report m) {p e : ℕ} {x : W → Room}
  {γ : ℝ} {L : Meter W} {gross : W → ℝ≥0∞} [∀ w, Fintype (Y w)]

private theorem zeroRank {P : ℝ} {I J : Type} (D : Deck P I J) (T : Packet I 0) :
    note (D.scroll T) = note T := by
  unfold note Deck.scroll Stalk.collect
  let t : Stalk D.project Fin.elim0 := ⟨Fin.elim0, Subsingleton.elim ..⟩
  rw [tsum_eq_single t]
  · change D.dyed T Fin.elim0 = T Fin.elim0
    simp [Deck.dyed, Deck.polish]
  · exact fun b hb => (hb (Subsingleton.elim ..)).elim

theorem original (F : Margins Y) (H : S.Epoch F L 0 p)
    (vac : ∀ w, Vacuum (T.orb (Page.finallyW M w)))
    (quiet : ∀ e, e ≤ p → ∀ r, Workday L (S.landQ 0) (fun w => S.stump T F w e r))
    (cover : ∀ i, i ≤ p → ∀ r, 0 < r → Claim (coverL M L) (S.coverQ x 2)
      (WilsonIndependentFreshFiniteWage.credit S γ gross) (fun j => Z.main j i r))
    (wind : ∀ i, i ≤ p → ∀ r, Claim (coverL M L) (S.markUp x 0)
      (fun j => gross j.bindW * ENNReal.ofReal ((S.l (Page.opening M j.bindW) / S.P j.bindW)^γ))
      (fun j => Z.deviation j i r))
    (stop : Choice M) (board : ∀ w, S.l (stop.choose w) ≤ S.P w)
    (hg : 0 ≤ γ) (he : e ≤ p) :
    Carry L (fun w => WilsonIndependentFreshFiniteWage.credit S γ gross (stop.choose w))
      (fun w => ‖S.vista T Z F w e - note (Z.main (Page.finallyW M w) e 0)‖ₑ) := by
  let endAt := Page.finallyW M
  let rent w := WilsonIndependentFreshFiniteWage.credit S γ gross (stop.choose w)
  have cheaper (w : W) (y : ℝ) (hy : S.l (stop.choose w) ≤ y) :
      gross w * ENNReal.ofReal ((S.l (Page.opening M w) / y)^γ) ≤ rent w := by
    apply mul_le_mul_right
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow (by have := S.hl (Page.opening M w); have := (S.hl (stop.choose w)).trans_le hy; positivity) _ hg
    exact div_le_div_of_nonneg_left (S.hl _).le (S.hl _) hy
  have finiteWind (i : ℕ) (hi : i ≤ p) (r : ℕ) : Claim L (fun w => S.markUp x 0 (endAt w)) rent
      (fun w => Z.deviation (endAt w) i r) := by
    apply Carry.charge ((wind i hi r).us endAt)
    apply Carry.mono (Carry.unit ..)
    intro w
    exact cheaper w _ (board w)
  have fold (i : ℕ) (hi : i ≤ p) (r : ℕ) (hr : 0 < r) : Claim L (fun w => S.markUp x 0 (endAt w)) rent
      (fun w => (S.maps (endAt w)).scroll (Z.main (endAt w) i r)) := by
    let P : Post (fun w => _) (fun w => _) :=
      ⟨S.P, S.hp, fun w => S.radius (endAt w), fun w => S.radius_pos (endAt w), fun w => S.maps (endAt w)⟩
    have h := (cover i hi r hr).us endAt
    apply Carry.charge (P.folded_claim x (u := 0) (P.narrower x (b := 2) h (by omega)))
    apply Carry.mono (Carry.unit ..)
    intro w
    exact cheaper w _ (S.tails (stop.choose w))
  have paid (i : ℕ) (hi : i ≤ p) (r : ℕ) (hr : 0 < r) : Claim L (fun w => S.markUp x 0 (endAt w)) rent
      (fun w => Z.point (endAt w) i r) := by
    convert Claim.add (finiteWind i hi r) (fold i hi r hr) using 1
    ext1 w
    unfold Accounts.Report.deviation
    rw [sub_add_cancel]
  have h₁ := WilsonIndependentFiniteHaar.original S T Z F H vac quiet paid he
  let f w := note (Z.point (endAt w) e 0)
  let g w := note (Z.main (endAt w) e 0)
  have h₂ : Carry L rent (fun w => ‖f w - g w‖ₑ) := by
    apply Carry.mono (finiteWind e he 0)
    intro w
    dsimp only
    rw [quotaNote]
    unfold f g
    rw [← zeroRank (S.maps (endAt w))]
    exact le_rfl
  apply Carry.mono (Carry.add h₁ h₂)
  intro w
  apply le_trans _ (enorm_add_le (S.vista T Z F w e - f w) (f w - g w))
  exact le_of_eq (congr_arg (enorm (E := ℝ)) (by dsimp [g]; abel))

end YM.Integration.WilsonIndependentFreshFoldedHaar
