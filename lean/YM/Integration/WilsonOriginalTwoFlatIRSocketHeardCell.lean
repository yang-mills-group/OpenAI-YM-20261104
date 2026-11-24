import YM.Integration.WilsonOriginalTwoFlatIRSocketAbsolute
import YM.Integration.WilsonOriginalTwoFlatIRFlatMarked
import YM.Integration.WilsonMaxwellThermometerNominatedSecant

/-! The incumbent and the held receipt on the same absolute reporting cell. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRSocketHeardCell
open Function Finset Set Table Lattice RG Wilson Source Labels Extra.Histories Motion Extraction
open PhysicalNext.Repeat.Legato WilsonMatrixTicketLanesQuota WilsonPositionThermometerGradedSource
open WilsonThermometerOffsetTrajectory WilsonAddressedAlignedColumn WilsonThermometerUnitFilingCoarse
open RG16 RG16.Literal
open WilsonOriginalTwoFlatIRFlatMarked (seat)
open WilsonReflectedPublicOrientedFaces (displayed)
open WilsonThermometerReflectedTrajectory (anchorAt)
open WilsonMaxwellThermometerNominatedSecant WilsonPositionThermometerConnected
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){N per f K u:ℕ}
local notation "C" => R.family
private abbrev grades (i:Fin 3) := (grade i).val
local notation "Mode" => Finset (Fin 3)

def row (Y:(i:Fin 3) → (C).label (grades i))(turn:Fin 3 → Motion)
    (p:WilsonCenteredPhysicalPanel.Sites R (f,per) 3)(s:Mode):Config G ((C).side N per) → ℂ:=
  WilsonMeasuredPublicEntranceCellWords.physical R grades Y turn p (seat s)

def incumbent (Y:(i:Fin 3) → (C).label (grades i))(turn:Fin 3 → Motion)
    (p:WilsonCenteredPhysicalPanel.Sites R (f,per) 3)(s:Mode):ℂ:=(C).omega N per (row R Y turn p s)

def held (kn:K≤N)(uk:u≤K)(Y:(i:Fin 3) → (C).label (grades i))(turn:Fin 3 → Motion)
    (p:WilsonCenteredPhysicalPanel.Sites R (f,per) 3)(s:Mode):ℂ:=
  reading R (N:=N) (credit C N per 0 (row R Y turn p s) K kn) u uk

theorem named (live:f≤N)(Y:(i:Fin 3) → (C).label (grades i))(turn:Fin 3 → Motion)
    (p:WilsonCenteredPhysicalPanel.Sites R (f,per) 3)(s:Mode)(A:WilsonPositionThermometerCapStation.Group C 6)
    (paid:∀i,displayed R (grades i) (Y i) (turn i)=WilsonNeutralOffsetCutoff.named R A N per i):
    incumbent R (N:=N) Y turn p s=WilsonOriginalTwoFlatRoseCentered.ordinary R A N per
      (fun i=>((C).S.toDepth live per).embed (p i)) s:=by
  unfold incumbent row WilsonMeasuredPublicEntranceCellWords.physical WilsonOriginalTwoFlatRoseCentered.ordinary
  congr 1
  funext U
  apply Finset.prod_congr rfl
  intro i _
  rw [paid i]
  congr 1
  simp only [anchorAt,Mix.camp,dif_pos live]

theorem seven (p q:Mode → ℂ)(T A ε:ℝ)(en:0≤ε)(small:ε≤A)
    (known:∀s:Mode,‖p s‖≤T)(bought:∀s:Mode,s.Nonempty → ‖p s-q s‖≤ε):
    let M:=max 1 (max T (T+A))
    ‖value p-value q‖≤7*(M+2*M^2)*ε:=by
  intro M
  have single(i:Fin 3):‖q {i}‖≤T+A:=by
    have diff:‖q {i}-p {i}‖≤A:=by rw [norm_sub_rev];exact (bought _ (singleton_nonempty i)).trans small
    exact (norm_le_norm_sub_add (q {i}) (p {i})).trans ((add_le_add diff (known _)).trans_eq (add_comm _ _))
  have count:=budget p q T (T+A) (fun s _ _=>known s) single
  rw [signed]
  refine (norm_sum_le ..).trans ?_
  calc
    (∑s:Mode,‖bill p q s*(p s-q s)‖)≤∑s:Mode,‖bill p q s‖*ε:=by
      apply Finset.sum_le_sum
      intro s _
      rw [norm_mul]
      by_cases live:s.Nonempty
      · exact mul_le_mul_of_nonneg_left (bought s live) (norm_nonneg _)
      · rw [Finset.not_nonempty_iff_eq_empty.mp live]
        have clear:bill p q ∅=0:=by
          have none(i:Fin 7):(∅:Mode)≠faceKey i:=by fin_cases i <;> decide
          simp [bill,none]
        simp [clear]
    _=(∑s:Mode,‖bill p q s‖)*ε:=(Finset.sum_mul ..).symm
    _≤_:=mul_le_mul_of_nonneg_right count en

end YM.Integration.WilsonOriginalTwoFlatIRSocketHeardCell
end
