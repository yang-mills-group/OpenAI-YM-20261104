import YM.Integration.WilsonOriginalTwoFlatIRStopped
import YM.Integration.WilsonOriginalTwoFlatGridScaling
import YM.Integration.WilsonOriginalTwoFlatTelescope

/-! The original moment is compared directly to the final scalar of the
complete ordinary word. The fixed and moving readings use the same Haar
numerator, including all of its earlier nonconstant-to-unit deposits. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRHeard
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels
open Planned.GuardedAtom Extra.Histories Next.Foundations
open RG16 RG16.Literal Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFlatTelescope
open WilsonOriginalTwoFlatTelescope WilsonOriginalTwoFlatGridScaling
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){N per K c u v:ℕ}
local notation "C" => R.family
local notation "X" j:max => Config G ((C).side j per)
local notation "read" j:max M:max b:max h:max =>
  reading R (N:=N) (numerator R N per j M) b h

theorem terminal (uc:u≤c)(vc:v≤c)(ck:c≤K)(kn:K≤N)
    (Y:Cut C N per)(cont:Continuous Y)(M:∀j:ℕ,(X j)→ℂ)
    (paid:∀j,min u v≤j→j≤K→Integrable (numerator R N per j (M j)) (prior G _))
    {A B E:ℝ}(phase:‖gap R N per u ((uc.trans ck).trans kn) Y‖≤A)
    (entry:entrance R Y (uc.trans ck) kn M≤B)
    (transfer:‖read c (M c) u uc-read c (M c) v vc‖≤E):
    ‖(C).omega N per Y-M v 1‖≤
      A+B+(∑j∈Ico c K,‖feeAt R N per u M j‖)+E+(∑j∈Ico v c,‖feeAt R N per v M j‖):=by
  let W:=(C).omega N per Y
  let f:=reading R (N:=N) (credit C N per 0 Y K kn) u (uc.trans ck)
  let h:=read K (M K) u (uc.trans ck)
  let a:=read c (M c) u uc
  let b:=read c (M c) v vc
  have same:reading R (N:=N) (credit C N per 0 Y u ((uc.trans ck).trans kn)) u le_rfl=f:=by
    dsimp only [f,reading]
    rw [cutoff R _ le_rfl Y cont,cutoff R kn (uc.trans ck) Y cont]
  have p:‖W-f‖≤A:=by simpa only [gap,same] using phase
  have k:‖f-h‖≤B:=entry
  have top:‖h-a‖≤∑j∈Ico c K,‖feeAt R N per u M j‖:=by
    rw [show h-a=∑j∈Ico c K,feeAt R N per u M j from interval R uc ck kn M
      (fun j cj jk=>paid j (((min_le_left _ _).trans uc).trans cj) jk)]
    exact norm_sum_le _ _
  have final:read v (M v) v le_rfl=M v 1:=by
    have normed:read v (M v) v le_rfl=actualTransport C (N:=N) (M v) le_rfl 1:=
      WilsonThermometerUnitFilingPosterior.weighted R (N:=N) (M v) le_rfl
    rw [normed,actualTransport_base C R.makes ((vc.trans ck).trans kn)]
  have last:‖b-M v 1‖≤∑j∈Ico v c,‖feeAt R N per v M j‖:=by
    rw [←final,show b-(read v (M v) v le_rfl)=∑j∈Ico v c,feeAt R N per v M j from interval R le_rfl vc (ck.trans kn) M
      (fun j vj jc=>paid j ((min_le_right _ _).trans vj) (jc.trans ck))]
    exact norm_sum_le _ _
  calc
    _≤‖W-b‖+‖b-M v 1‖:=norm_sub_le_norm_sub_add_norm_sub W b _
    _≤(((‖W-f‖+‖f-h‖)+‖h-a‖)+‖a-b‖)+‖b-M v 1‖:=by
      gcongr
      exact (norm_sub_le_norm_sub_add_norm_sub W a b).trans (add_le_add
        ((norm_sub_le_norm_sub_add_norm_sub W h a).trans (add_le_add (norm_sub_le_norm_sub_add_norm_sub W f h) (le_refl _))) (le_refl _))
    _≤_:=add_le_add (add_le_add (add_le_add (add_le_add p k) top) transfer) last

end YM.Integration.WilsonOriginalTwoFlatIRHeard
