import YM.Integration.WilsonOlderSignedOneMarkScalar
import YM.Integration.WilsonGeometricPrimaryReturn

/-! A gross hearing at the actual source. Its hard history drops out only on the tested clean field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullBareClean
open Function Filter Finset Lattice Wilson RG Marker QuadraticLocal Ac ConnectedActivityE6
open Extra.Histories Extra.Trajectories Labels Source Push.Local Trace.Physical.Germ
open ProjectorNext.Equivariance WilsonCapturedPrimaryReading
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {V X ι:Type} [Fintype V] [DecidableEq V]
  {P:Rep G n} {o:V→Site n} {R:Census V} (A:Gallery X ι o P R)
theorem hearing {w:V→ℝ} {E K a:ℝ} (hw:∀v,0<w v) (ha:0≤a)
    (reg:A.E.Paid w P.p.B a E) (hard:A.K.Paid w P.p.B P.p.supportExponent K)
    (z:ℂ) (x:X) (v:V) (U:Config G n) (clear:flags P.p.threshold U=∅) :
    ‖z*((A.density x U).part (R.fire v))/(P.eval U:ℂ)‖ ≤
      ‖z‖*(E/Poly.toll w (R.fire v)) :=by
  let s:=R.fire v
  have charge:=WilsonFirstReceivedGalleryRegular.occupied A.E reg ha hw x U s v
    (Finset.mem_singleton_self v)
  have live:(P.eval U:ℂ)≠0:=noFlagEval clear
  have hs:=reg.sums ha hw x U
  have hk:=Hard.packet_summing A.K hard P.p.exponent_pos.le hw x U
  have exactRead:=WilsonCenteredSingletonMass.ordinary A x U v hs hk
  have empty:s≠R.quiet:=by
    intro h
    exact (Finset.singleton_nonempty v).ne_empty (congrArg Subtype.val h)
  have zero:((A.gas x U).part s)=0:=by
    rw [WilsonFirstReceivedGalleryRegular.clear A x U clear,Poly.one_part]
    exact if_neg empty
  change (A.density x U).part s=_ at exactRead
  rw [zero,mul_zero,add_zero] at exactRead
  rw [exactRead,← mul_assoc,mul_right_comm,mul_div_cancel_right₀ _ live,norm_mul]
  exact mul_le_mul_of_nonneg_left ((le_div_iff₀ (Poly.worth hw s)).mpr
    (by simpa only [mul_comm] using charge)) (norm_nonneg _)
end YM.Integration.WilsonOriginalNullBareClean
