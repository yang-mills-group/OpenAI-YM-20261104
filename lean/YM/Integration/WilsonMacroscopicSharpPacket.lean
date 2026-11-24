import YM.Integration.WilsonMacroscopicViewerCharge

/-! The sharp spatial remainder for the reader's exact retained packet, for every
state of the original phase algebra and a fixed separated macroscopic exterior. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicSharpPacket
open Function Set Filter MeasureTheory Table Extraction OPE OPE.Orbits OPE.Orbits.Reader OPE.Log
open scoped Topology BigOperators Classical
open private trunc_fields from YM.OPE.Orbits.System
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
    (F : Spec.Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {I J : Type} [Fintype I] [Fintype J] {d : I → ℕ} {e : J → ℕ}

def Sharp (h : ℕ) (v : Labels S d) (w : Labels S e) (M η δ : ℝ) : Prop :=
    ∃ (k : ℕ) (A : ℝ), 0 < A ∧ ∀ᶠ r : ℝ in 𝓝[>]0, ∀ (x:I→E4) (o:E4) (y:J→E4),
      WithinRoom r M η x o → ClearOf o y δ →
      ‖algebraError F Q x o v y w h‖ ≤ A * badge r ^ k * r ^ ((h:ℝ)+1-weight d) ∧
      ∀ q : Viewers F,
        ‖whole (spectator F q) x v y w - upon (spectator F q) h o y w (Q.packet h x v o)‖ ≤
          A * badge r ^ k * r ^ ((h:ℝ)+1-weight d)

theorem original (paid : Services C f S) (foundation : Foundation F Q) (h : ℕ)
    (v : Labels S d) (w : Labels S e) {M η δ : ℝ}
    (hM : 0 ≤ M) (hη : 0 < η) (hδ : 0 < δ)
    (head : WilsonMacroscopicLoggedRow.Priced F Q v (h+1) M η) : Sharp F Q h v w M η δ := by
  obtain ⟨D,hD,recv⟩ := WilsonMacroscopicViewerCharge.uniform F paid (h+1) w hδ
  obtain ⟨k,B,hB,row⟩ := WilsonMacroscopicLoggedRow.original F Q v paid hM hη (h+1) head
  have next := foundation.discrepancy I J d e v w M η δ (1/2) hM hη hδ (by norm_num) (h+1)
  refine ⟨k, 1+D*B, by positivity, ?_⟩
  filter_upwards [row,next,(show ∀ᶠ r:ℝ in 𝓝[>]0,0<r from self_mem_nhdsWithin),
    ((ge_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds)] with r row next hr small x o y fit clear
  have issued := next x o y fit clear
  have distinct := issued.2.1
  have hrow := row x o fit
  simp only [Nat.cast_add,Nat.cast_one] at issued hrow
  have money : 1 ≤ badge r := by unfold badge run;linarith [Real.log_nonpos hr.le small]
  let T := badge r ^ k * r ^ ((h:ℝ)+1-weight d)
  have tpos : 0 ≤ T := mul_nonneg (pow_nonneg (by linarith) _) (Real.rpow_nonneg hr.le _)
  have margin : r ^ ((h:ℝ)+1+1-weight d-1/2) ≤ T := calc
    _ ≤ r ^ ((h:ℝ)+1-weight d) := Real.rpow_le_rpow_of_exponent_ge hr small (by linarith)
    _ ≤ _ := le_mul_of_one_le_left (Real.rpow_nonneg hr.le _) (one_le_pow₀ money)
  have formula_paid (q : Viewers F) :
      ‖formula F Q x o v y w h q‖ ≤ (1+D*B) * T := by
    have lift : formula F Q x o v y w h q =
        formula F Q x o v y w (h+1) q + upon (spectator F q) (h+1) o y w (Q.fresh (h+1) x o v) := by
      have split : trunc (spectator F q) F Q (h+1) x o v y w =
          trunc (spectator F q) F Q h x o v y w + upon (spectator F q) (h+1) o y w (Q.fresh (h+1) x o v) := by
        rw [trunc_fields,trunc_fields,Fin.sum_univ_castSucc]
        rfl
      unfold formula
      rw [split]
      abel
    rw [lift]
    calc
      _ ≤ _ := norm_add_le _ _
      _ ≤ T + D * (B * T) := add_le_add ((issued.2.2.2 q).trans margin)
        ((recv o y clear distinct q _).trans (mul_le_mul_of_nonneg_left (by simpa only [T,mul_assoc] using hrow) hD))
      _ = (1+D*B)*T := by ring
  have hpos : 0 ≤ (1+D*B)*T := by positivity
  constructor
  · rw [mul_assoc]
    apply (glance_contract F hpos).2
    intro q
    rw [formula_seen F Q x o v y w h q issued.1 distinct]
    exact formula_paid q
  · intro q
    rw [packet_read F Q x o v y w q h distinct,mul_assoc]
    exact formula_paid q

/-- A logarithmic matrix ticket on this same extracted physical hierarchy prices
each raw grade on the original prescription carried by the public reader. -/
theorem on_ticket (built : Facilities C f S) (foundation : Foundation F Q) {u : Filter (ℕ×ℕ)}
    [u.NeBot] (hu : u ≤ f.fuse) (ticket : MatrixTicket (C:=C) S F.sector.derivatives u)
    (h : ℕ) (v : Labels S d) (w : Labels S e) {M η δ : ℝ}
    (hM : 0 ≤ M) (hη : 0 < η) (hδ : 0 < δ) : Sharp F Q h v w M η δ :=
  original F Q built.toServices foundation h v w hM hη hδ
    (WilsonMacroscopicLoggedRow.issued F Q v (first_log F built hu ticket Q.spans) hM hη (h+1))

end YM.Integration.WilsonMacroscopicSharpPacket
