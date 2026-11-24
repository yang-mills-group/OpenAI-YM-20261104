import YM.Integration.WilsonReflectedPublicCommonDose

/-! Apply the same positive dose to the actual deposited ultraviolet row and the
separately reserved unit discrepancy of its reported inverse column. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicCommonRows
open Trace.Physical.GermGraph
open Function Lattice Wilson RG Source Labels Extra.Histories Extra.Histories.Relay
open MergeProof Push.Local RG05Readout RG05Readout.Address Motion PhysicalNext.Repeat.Legato
open WilsonReflectedFundedHearing WilsonReflectedPublicSignedFare WilsonReflectedPublicGuardedColumns
open WilsonReflectedPublicCommonDose WilsonReflectedOpticalArm
variable {G:Gauge}(R:Run G){N p f K d:ℕ}
local notation "P_" => R.family.path.rep N p f
local notation "F_" => R.family.labels.level d

theorem original (A:Arm R d N p f K)(hf:f ≤ K)(top:K ≤ N)
    (χ C V a:ℝ)(hp:1 ≤ χ)(ap:0 ≤ a)
    (row:Three G (R.family.side f p))(wallet head:ℝ)
    (Q E:Coefficient (F_) (R.family.side f p))
    (form:Q.Format A.o R.family.params P_)
    (size:(F_).coeffSize Q.x ≤ head)(paid:Q.remBound A.o P_ (safety R.family f) wallet)
    (soft:row.2.1=Q.exponentialEntry A.o (R.family.localSection d) P_)
    (born:profile (P_).activities row.2.2=profile (P_).activities Q.forced)
    (written:Q.density A.o (R.family.localSection d) P_=row.1)
    (read:∀U,row.1 U=(χ:ℂ)⁻¹*((P_).eval U:ℂ)*WilsonReflectedOriginalTwoDeposit.held R
      (source R A (hf.trans top)) f U)
    (unit:Restored R A hf top 1 (a*C*V) E):
    let c:=dose χ C V
    let θ:ℂ:=(c*χ:ℝ)
    Joined R A hf top (c:ℂ) (θ • row) wallet head a (stretch θ Q) (stretch (c:ℂ) E):=by
  intro c θ
  have small:=smaller χ C V hp
  have normθ:‖θ‖ ≤ 1:=by rw [Complex.norm_real,Real.norm_of_nonneg small.2.1]; exact small.2.2.1
  have inv:=invoice_stretch Q A.o (R.family.localSection d) (P_) θ
  apply deposited R A hf top (c:ℂ) (θ • row) (stretch θ Q) (stretch (c:ℂ) E) (stretch_format θ form)
  · change (F_).coeffSize (θ • Q.x) ≤ head
    rw [Size.smul]
    exact (mul_le_of_le_one_left (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) normθ).trans size
  · exact rem_mono (stretch_rem θ paid) (mul_le_of_le_one_left (rem_nonneg paid) normθ)
  · exact (congrArg (fun v=>θ • v) soft).trans ((congrArg (fun z=>z.2.1) inv).symm)
  · change profile (P_).activities (θ • row.2.2)=profile (P_).activities (θ • Q.forced)
    rw [profile_scale,profile_scale,born]
  · exact (congrArg (fun z=>z.1) inv).trans (congrArg (fun v=>θ • v) written)
  · intro U
    change θ*row.1 U=_
    rw [read]
    have same:θ*(χ:ℂ)⁻¹=(c:ℂ):=composed χ C V hp
    rw [←same]
    ring
  · exact scaled R A hf top χ C V hp a ap E unit

end YM.Integration.WilsonReflectedPublicCommonRows
end
