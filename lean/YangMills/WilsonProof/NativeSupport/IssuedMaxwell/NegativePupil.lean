import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.PositionStore
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.NegativePupil
open YM YM.XSpace
open YangMills.MSbar Function Set
open IssuedMaxwell.Reports (B)
variable {g:YangMills.GaugeGroup}{n:ℕ}

theorem support (t:Test n):tsupport (fun x=>(t x).re) ⊆ tsupport t:=by
  apply closure_mono
  intro x nonzero zero
  exact nonzero (congrArg Complex.re zero)

def real (t:Test n):RealTest n:=
  ⟨fun x=>(t x).re,Complex.reCLM.contDiff.comp t.contDiff,
    t.hasCompactSupport.of_isClosed_subset isClosed_closure (support t),(support t).trans t.tsupport_subset⟩

theorem original (P:PositionPrescription (B g))(H:Admissible P):
    Rose.Turns (real P.triangle.profile) ∧
    tsupport (real P.triangle.profile) ⊆ Rose.spot P.triangle.cut ∧
    ∀x,(real P.triangle.profile x:ℂ)=P.triangle.profile x:=by
  refine ⟨fun V x=>congrArg Complex.re (H.calibration.turns V x),?_,?_⟩
  · intro x hx
    have gap:=H.calibration.separated x (support _ hx)
    constructor
    · intro a b hab
      exact (le_max_right ..).trans_lt (gap a b hab)
    · intro a b hab
      have hh:= (le_max_left ..).trans_lt (gap a b hab)
      calc
        (5:ℝ)*(4/5)=4 := by norm_num
        _ < _ := hh
  · intro x
    apply Complex.ext
    · rfl
    · exact (H.calibration.realValue x).symm
end IssuedMaxwell.NegativePupil
end
