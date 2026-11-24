import YM.Integration.WilsonMatrixTicketLanesNormalizedFleetInvoice
import YM.RG02.Marker.Euler
import YM.FormalOPE.RG10.MarkerLog

/-! Separate the regular coefficient from the marked compatible gas on every held field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesNormalizedFleetLog

open OPE Strobe Yarn Vista26 Function Filter Set MeasureTheory Finset Lattice Wilson RG Push
open Marker Source Extra.Histories Extra.Trajectories Motion Local Bid Cells Overlay MergeProof
open Accent Ribbons ManyCopies Patrol GridApprox GridApprox.Nil AbsoluteSums
open WilsonMatrixTicketLanesNormalizedFleetInvoice
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

def divided {J : Census V} (X : Poly J) : Poly J := (X.part J.quiet)⁻¹ • X

private theorem log_product {J : Census V} (A K : Poly J) (quiet : A.part J.quiet = 0)
    (e : ℂ) (ne : e ≠ 0) (pos : (e • (Poly.pass A * K)).part J.quiet ≠ 0) :
    connected (divided (e • (Poly.pass A * K))) = A + connected (divided K) := by
  have mass : (e • (Poly.pass A * K)).part J.quiet = e * K.part J.quiet := by
    rw [Poly.part_smul,Poly.quiet_mul,Poly.pass_part _ quiet,one_mul]
  have nk : K.part J.quiet ≠ 0 := by
    intro zero
    exact pos (by rw [mass,zero,mul_zero])
  have eq : divided (e • (Poly.pass A * K)) = Poly.pass A * divided K := by
    unfold divided
    rw [mass,smul_smul,mul_smul_comm]
    congr 1
    field_simp
  rw [eq,RG02.Marks.connected_mul (Poly.pass_part _ quiet)
    (by simp only [divided,Poly.part_smul,inv_mul_cancel₀ nk]),
    FormalOPE.RG10.PolyUtil.conn_pass _ quiet]

def hard {J : Census V} (R : Rep G n) (ray : V → Box n → Config G n → ℂ)
    (Z : Box n → Config G n → Poly J) (U : Config G n) : Poly J :=
  field (fun X => bar R.activities J U X + Mach J (fun i => ray i X U) + Z X U)
    (flags R.p.threshold U)

theorem original {P : Brigade n V} {R : Rep G n} {Q : Config G n → Poly (Names V I)}
    {o : I → Site n} {S : I → Lamp G n} {w : I → ℝ} (bought : Fleet P R Q o S w) :
    ∃ F Z, Q = restore R (P.lamp S) (P.ray R S) F Z ∧
      Carton (P.place o) F Z R.p.threshold ∧
      Charge (P.place o) (w ∘ Prod.snd) Prod.fst Z R.p.B (R.p.supportExponent - 3) ∧
      ∀ U, (Q U).part (Names V I).quiet ≠ 0 → ∀ s : (Names V I).Mode, 2 ≤ s.val.card →
        (connected (divided (Q U))).part s - (connected (divided (hard R (P.ray R S) Z U))).part s =
          ∑ X, (F X U).part s ∧
        (0 ≤ R.p.supportExponent - 3 →
          Poly.toll (w ∘ Prod.snd) s *
            ‖(connected (divided (Q U))).part s - (connected (divided (hard R (P.ray R S) Z U))).part s‖ ≤ 1) := by
  obtain ⟨F,Z,issued,carton,feeF,feeZ⟩ :=
    WilsonMatrixTicketLanesNormalizedFleetInvoice.original bought
  refine ⟨F,Z,issued,carton,feeZ,?_⟩
  intro U pos s two
  let A := Mach (Names V I) (fun i => P.lamp S i U) + ∑ X, F X U
  have quiet : A.part (Names V I).quiet = 0 := by
    dsimp only [A]
    rw [Poly.part_plus,mute,Poly.part_sum]
    simp only [(carton.exp _).1.sil, sum_const_zero, add_zero]
  have fieldAt : Q U = (Real.exp (R.exponent U) : ℂ) • (Poly.pass A * hard R (P.ray R S) Z U) :=
    congrFun issued U
  have eq := log_product A (hard R (P.ray R S) Z U) quiet _ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
    (fieldAt ▸ pos)
  have part : (connected (divided (Q U))).part s - (connected (divided (hard R (P.ray R S) Z U))).part s =
      ∑ X, (F X U).part s := by
    rw [fieldAt,eq,Poly.part_plus,add_sub_cancel_right]
    dsimp only [A]
    rw [Poly.part_plus,hush _ _ two,zero_add,Poly.part_sum]
  refine ⟨part,?_⟩
  intro expo
  obtain ⟨v,member⟩ := Finset.card_pos.mp (by omega : 0 < s.val.card)
  have fare := (feeF s v member U).2
  have money := (Poly.worth (fun v : V × I => bought.secure v.2) s).le
  rw [part]
  calc
    _ ≤ Poly.toll (w ∘ Prod.snd) s * (∑ X, ‖(F X U).part s‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) money
    _ ≤ 1 := by
      rw [Finset.mul_sum]
      refine le_trans (Finset.sum_le_sum fun X _ => ?_) fare
      exact le_mul_of_one_le_right (mul_nonneg money (norm_nonneg _))
        (Real.one_le_exp (mul_nonneg expo (Nat.cast_nonneg _)))

end YM.Integration.WilsonMatrixTicketLanesNormalizedFleetLog
