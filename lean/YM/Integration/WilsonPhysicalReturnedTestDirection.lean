import YM.Integration.WilsonCapturedPrimaryMasterGridGross
import YM.Integration.WilsonPhysicalSampledTestDirection

/-! The full periodic K-site sum for a smooth directional derivative on a
genuine three-name fitted Wilson reading in the inherited N-vacuum. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalReturnedTestDirection
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open PhysicalNext.Repeat.Legato RG16 RG16.Literal
open WilsonMovingForkMixedSeed WilsonAddressedFiniteGuardTrial WilsonPositionProgramReportedField
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceCellWords (submitted)
open WilsonOriginalMicroscopicGuardedWallet (loss)
open LocalLTE.Weft WilsonPosteriorProjectionStencil WilsonSmoothUnitFiniteGrid
open WilsonSmoothUnitLatticeDifference (coef)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 3  →  ℕ){N per f K requested power t:ℕ}{B:ℝ}{fk:f≤K}{cut:K≤N}
variable (A:Panel R d N per f K fk cut requested power t B)(file:Filed R d K)
  (station:A.slot=file.station)(axes:A.axis=file.A N per)
variable (s:(Stock.census (Fin 3)).Mode)(sites:Fin 3  →  Site (R.family.side K per))(slot:Fin 3)(axis:Axis)
  {b:ℕ}(stop:b≤K)(W:Config G (R.family.side b per))

def value (R:Run G)(d:Fin 3  →  ℕ){N per f K requested power t:ℕ}{B:ℝ}{fk:f≤K}{cut:K≤N}
    (A:Panel R d N per f K fk cut requested power t B)(file:Filed R d K)
    (s:(Stock.census (Fin 3)).Mode)(sites:Fin 3  →  Site ((R.family).side K per))
    (slot:Fin 3)(axis:Axis){b:ℕ}(stop:b≤K)(W:Config G ((R.family).side b per))
    (x:Per ((R.family).side K per)):ℂ:=
  actualTransport R.family (N:=N) (submitted R d (N:=N) file (le_refl K) A.names A.turn
    (Function.update sites slot (Function.update (sites slot) axis x)) s) stop W

include station axes in
theorem held (x:Per (R.family.side K per)):
    ‖value R d A file s sites slot axis stop W x‖≤∏i∈s.val,loss R (d i) K*(B*(R.family.path.levels.clock.hatBeta K) ^ power):=by
  unfold value
  apply actualTransport_norm_le R.family R.makes cut _ stop W
  intro U
  exact WilsonCapturedPrimaryMasterGridGross.original R d A file station axes s _ U

include station axes in
/-- The original observation controls every stage and physical period. The
only derivatives in its price are derivatives of the test. Choosing j=2
retains the nonconstant descendant with every other arm on this same law. -/
theorem original (k:ℕ)(j:J k)(left ρ:ℝ)(rpos:0<ρ)(fit:width k≤(R.family.side K per).val)
    (φ:ℝ  →  ℝ)(regular:ContDiff ℝ (↑(2*k+1):WithTop ℕ∞) φ)
    (clear:∀y:ℝ,y≤left+(width k:ℝ)*(R.family.S.a K/ρ) ∨ left+((R.family.side K per).val:ℝ)*(R.family.S.a K/ρ)≤y  →  φ y=0)
    (mass:Per (R.family.side K per)  →  ℝ)(nonneg:∀z,0 ≤ mass z)
    (heads:∀z y,y∈Icc (point left (R.family.S.a K/ρ) z) (point left (R.family.S.a K/ρ) z+(width k:ℝ)*(R.family.S.a K/ρ))  → 
        ‖iteratedDeriv (2*k+1) φ y‖≤ mass z):
    let h:=R.family.S.a K/ρ
    let span:=(width k:ℝ)*h
    let F:=value R d A file s sites slot axis stop W
    ‖(∑z:Per (R.family.side K per),((coef φ (point left h z) j.val*span ^ j.val:ℝ):ℂ)*F z)-
      ∑z:Per (R.family.side K per),(φ (point left h z):ℂ)*∑i:J k,(weight k i j:ℂ)*F (z-(offset i:Per (R.family.side K per)))‖≤
      cost k j*span ^ (2*k+1)*(∑z,mass z)*(∏i∈s.val,loss R (d i) K*(B*(R.family.path.levels.clock.hatBeta K) ^ power)):=by
  let h:=R.family.S.a K/ρ
  let span:=(width k:ℝ)*h
  let F:=value R d A file s sites slot axis stop W
  have hp:0<h:=div_pos (R.family.S.a_pos K) rpos
  let gross:=∏i∈s.val,loss R (d i) K*(B*(R.family.path.levels.clock.hatBeta K) ^ power)
  have fee:0≤cost k j*span ^ (2*k+1):=mul_nonneg (sum_nonneg fun _ _=>abs_nonneg _) (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hp.le) _)
  have cap:(∑x,mass x*‖F x‖)≤(∑x,mass x)*gross:=by
    rw [Finset.sum_mul]
    exact sum_le_sum fun x _=>mul_le_mul_of_nonneg_left (held R d A file station axes s sites slot axis stop W x) (nonneg x)
  have row:=WilsonPhysicalSampledTestDirection.original k j left h hp fit φ regular clear F mass nonneg heads
  exact row.trans ((mul_le_mul_of_nonneg_left cap fee).trans_eq (mul_assoc _ _ _).symm)

end YM.Integration.WilsonPhysicalReturnedTestDirection
