import YM.Integration.SelectedPlanIntrinsicRenderCost

/-! The native unit/shift bills apply to the original unchanged activity list
at the supplied norm. No physical row, forced activity or stored credit is
changed by these validity conclusions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedPlanIntrinsicRenderValidity
open Lattice Wilson RG IterationFour IterationFour.Vacuum
open LocalComparison.Global ZeroAwareIntrinsicRenderInvoice

private theorem enlarge {G : Gauge} {n : Side} {E : Activities G n}
    {p : BudgetPoint} {d d' z : ℝ} (h : E.Valid p d z) (hd : d ≤ d') :
    E.Valid p d' z := by
  refine ⟨h.regular, h.forced, h.moves, ?_, h.boundK⟩
  obtain ⟨v, hv, hsum⟩ := h.boundE
  exact ⟨v, hv, fun x => ⟨(hsum x).1, (hsum x).2.1, (hsum x).2.2.trans hd⟩⟩

private theorem dollars_repriced {G : Gauge} {n : Side}
    (c : Piece G n → ℝ) (S : List (Piece G n)) (k : ℤ → ℝ) :
    Render.dollars (fun a => ‖weight k a‖) (repriceLayers c S) =
      (S.map (fun a => ‖weight k a‖ * c a)).sum := by
  induction S with
  | nil => rfl
  | cons a S ih =>
      change ‖weight k a‖ * c a +
          Render.dollars (fun a => ‖weight k a‖) (repriceLayers c S) =
        ‖weight k a‖ * c a + (S.map (fun a => ‖weight k a‖ * c a)).sum
      rw [ih]

private theorem capped_permits {G : Gauge} {n : Side} {S : List (Piece G n)}
    {p : BudgetPoint} {rankCap : ℕ} {width budget : ℝ}
    (H : ZeroAwareVacuumPackets S p rankCap width budget)
    (h : Render.permits S p) (hw : 0 < width) :
    Render.permits (repriceLayers (ZeroAwareCappedRenderInvoice.credit H) S) p := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  exact ZeroAwareCappedRenderInvoice.invoice H h hw a ha

/-- The original beta-weighted activities have the exact intrinsic unit bill.
The forced family and its original budget remain unchanged. -/
theorem unit_valid {G : Gauge} {n : Side} {S : List (Piece G n)}
    {p : BudgetPoint} {rankCap : ℕ} {width budget d z b x : ℝ}
    (H : ZeroAwareVacuumPackets S p rankCap width budget)
    (h : Render.permits S p) (hw : 0 < width)
    (hb : 0 < b) (hx : x ∈ Currency.stripe b)
    (E : Activities G n) (hE : E.Valid p d z) :
    (Render.adorn (Render.prefactor (Currency.gain x)) E S).Valid p
      (d + Render.unitBill
        (repriceLayers (ZeroAwareCappedRenderInvoice.credit H) S) b) z := by
  have hpay := SelectedPlanIntrinsicRenderCost.activities_valid H h hw
    (fun e => Currency.gain x ^ e) E hE
  have hd := Render.unit_span
    (S := repriceLayers (ZeroAwareCappedRenderInvoice.credit H) S)
    (capped_permits H h hw) hb hx
  change Render.dollars (fun a => ‖weight (fun e => Currency.gain x ^ e) a‖)
    (repriceLayers (ZeroAwareCappedRenderInvoice.credit H) S) ≤ _ at hd
  rw [dollars_repriced] at hd
  exact enlarge hpay (add_le_add (le_refl d) hd)

/-- The exact difference on the same original list has the intrinsic shift
bill times the literal beta difference. -/
theorem shift_valid {G : Gauge} {n : Side} {S : List (Piece G n)}
    {p : BudgetPoint} {rankCap : ℕ} {width budget d z b x y : ℝ}
    (H : ZeroAwareVacuumPackets S p rankCap width budget)
    (h : Render.permits S p) (hw : 0 < width)
    (hb : 0 < b) (hx : x ∈ Currency.stripe b) (hy : y ∈ Currency.stripe b)
    (E : Activities G n) (hE : E.Valid p d z) :
    (Render.adorn
      (Render.prefactor (Currency.gain x) - Render.prefactor (Currency.gain y)) E S).Valid p
      (d + Render.shiftBill
        (repriceLayers (ZeroAwareCappedRenderInvoice.credit H) S) b * |x-y|) z := by
  have hpay := SelectedPlanIntrinsicRenderCost.activities_valid H h hw
    (fun e => Currency.gain x ^ e - Currency.gain y ^ e) E hE
  have hd := Render.change_b
    (S := repriceLayers (ZeroAwareCappedRenderInvoice.credit H) S)
    (capped_permits H h hw) hb hx hy
  change Render.dollars
    (fun a => ‖weight (fun e => Currency.gain x ^ e - Currency.gain y ^ e) a‖)
    (repriceLayers (ZeroAwareCappedRenderInvoice.credit H) S) ≤ _ at hd
  rw [dollars_repriced] at hd
  exact enlarge hpay (add_le_add (le_refl d) hd)

end YM.Integration.SelectedPlanIntrinsicRenderValidity
end
