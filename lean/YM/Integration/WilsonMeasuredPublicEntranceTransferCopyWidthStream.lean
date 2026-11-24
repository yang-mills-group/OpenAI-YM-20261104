import YM.Integration.WilsonOriginalPublicTrialPhasePlates

/-! The restored original all-copy width across consecutive pre-capture steps. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferCopyWidthStream
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof MergeProof.Accent MergeProof.Menu Marker
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open RG05Readout RG05Readout.Address RG05Readout.Many RG05Readout.Pantry
open OPE.Therm Push.GridApprox PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open WilsonOriginalPublicTrialPhaseLanding

open scoped Topology ContDiff BigOperators Classical

open WilsonOriginalPublicTrialPhaseLanding (first)
open Legato.Bandage
variable {G:Gauge}

private theorem primary {w l B D:ℝ} (B0:0≤B) (d1:1≤D)
    (upper:w⁻¹≤D*B) (ticket:1+2*|l|≤B):(first w l)⁻¹≤D*B:=by
  by_cases compare:w≤1/(1+2*|l|)
  · simpa only [first,min_eq_left compare] using upper
  · rw [first,min_eq_right (le_of_not_ge compare),one_div,inv_inv]
    exact ticket.trans (le_mul_of_one_le_left B0 d1)

theorem original (S:Levels G) (j K:ℕ) (before:j≤K) (w l:ℕ → ℝ)
    (B H:ℝ) (h1:1≤H) (wpos:∀ (day : ℕ), (j ≤ day) → (day ≤ K) → 0 < w day)
    (opening:(w K)⁻¹≤B) (charged:∀ (day : ℕ), (j ≤ day) → (day < K) → 1+2*abs (l day) ≤ B)
    (hot:∀ (day : ℕ), (j ≤ day) → (day < K) → S.clock.hatBeta (day+1) ≤ H)
    (trace:∀ (day : ℕ), (j ≤ day) → (day < K) → w day=renal S day*first (w (day+1)) (l day)):
    (w j)⁻¹≤(H^2)^(K-j)*B:=by
  have b0:0≤B:=(inv_pos.mpr (wpos K before le_rfl)).le.trans opening
  have h0:=zero_le_one.trans h1
  have h2:1≤H^2:=one_le_pow₀ h1
  have chain:∀ (n day : ℕ), (j ≤ day) → (day+n = K) → (w day)⁻¹ ≤ (H^2)^n*B:=by
    intro n
    induction n with
    | zero=>
      intro i _ hi
      have eq:i=K:=by omega
      simpa [eq] using opening
    | succ n ih=>
      intro i ji endpt
      have live:i<K:=by omega
      have tail:=ih (i+1) (by omega) (by omega)
      have pos:=wpos (i+1) (by omega) (by omega)
      have hat:=S.fits.delayed (i+1)
      have hp:0<S.clock.hatBeta (i+1):=zero_lt_one.trans hat
      have reg:(renal S i)⁻¹=(S.clock.hatBeta (i+1))^2:=by
        unfold renal PhysicalNext.Repeat.Mallow.probe
        rw [Real.rpow_neg hp.le,inv_inv]
        norm_num
      have rmax:(renal S i)⁻¹≤H^2:=by rw [reg];gcongr;exact hot i ji live
      have _firstpos:=WilsonOriginalPublicTrialPhaseLanding.limits pos (l i)
      have spent:=primary b0 (one_le_pow₀ h2 (n:=n)) tail (charged i ji live)
      rw [trace i ji live,mul_inv_rev]
      calc
        _≤((H^2)^n*B)*(H^2):=mul_le_mul spent rmax (by rw [reg];positivity) (by positivity)
        _=(H^2)^(n+1)*B:=by ring
  exact chain (K-j) j le_rfl (by omega)

end YM.Integration.WilsonMeasuredPublicEntranceTransferCopyWidthStream
