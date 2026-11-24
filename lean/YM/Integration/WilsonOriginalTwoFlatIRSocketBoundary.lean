import YM.Integration.WilsonReceivedChronologicalFixedRoseBoundary

/-! Decompose the signed fitted physical boundary on one old density, before taking norms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRSocketBoundary
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker
open Extra.Histories Extra.Histories.Relay MergeProof MergeProof.Accent Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Legato
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonOriginalJointTrialHearing (fee)
open WilsonReceivedChronologicalFixedRoseBoundary (lower)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){V:Type}[DecidableEq V]{J:Census V}{I:Type}[Fintype I]
  {N per u b c K:ℕ}(amount:I → ℂ)(rows:I → (i:ℕ) → Config G (R.family.side i per) → Marker.Poly J)(s:J.Mode)
  (ub:u≤b)(bc:b<c)

def held:ℂ:=∑q,amount q*(((R.family.path.rep N per b).eval 1:ℂ)⁻¹*((rows q b 1).part s))

def shift:ℂ:=∑q,amount q*(reading R (N:=N) (fun U=>(rows q c U).part s) u (ub.trans bc.le)-
  reading R (N:=N) (fun U=>(rows q c U).part s) b bc.le)

def first:ℂ:=∑q,amount q*fee R N per (1:Config G (R.family.side u per)) (rows q) (K-1) s

def last:ℂ:=∑q,amount q*fee R N per (1:Config G (R.family.side b per)) (rows q) b s

local notation "sum₀" => ∑q,amount q*lower R (N:=N) (K:=K) (rows q) s ub bc
local notation "val₀" => held R (N:=N) (b:=b) amount rows s
local notation "step₀" => shift R (N:=N) amount rows s ub bc
local notation "rent₀" => first R (N:=N) (u:=u) (K:=K) amount rows s
local notation "cap₀" => last R (N:=N) (b:=b) amount rows s

theorem joined (original figure:ℂ):
    original-figure=(original-(sum₀))+((val₀)-figure)+(step₀)+(cap₀)+(rent₀):=by
  have base (q:I): reading R (N:=N) (fun U=>(rows q b U).part s) b le_rfl =
      ((R.family.path.rep N per b).eval 1:ℂ)⁻¹*((rows q b 1).part s):=by
    unfold reading
    rw [gust_base]
  simp only [held,shift,first,last,WilsonReceivedChronologicalFixedRoseBoundary.lower,base,mul_add,Finset.sum_add_distrib]
  ring

theorem estimate (original figure:ℂ)(a t d:ℝ)
    (inlet:‖original-(sum₀)‖≤a)(terminal:‖(val₀)-figure‖≤t)
    (cross:‖step₀‖≤d):
    ‖original-figure‖≤a+t+d+‖cap₀‖+‖rent₀‖:=by
  rw [joined R amount rows s ub bc original figure]
  calc
    _ ≤ (((‖original-(sum₀)‖+‖(val₀)-figure‖)+‖step₀‖)+‖cap₀‖)+‖rent₀‖:=by
      generalize original-(sum₀)=x
      generalize (val₀)-figure=y
      generalize (step₀)=z
      generalize (cap₀)=h
      generalize (rent₀)=w
      linarith only [norm_add_le x y,norm_add_le (x+y) z,norm_add_le (x+y+z) h,norm_add_le (x+y+z+h) w]
    _ ≤ _:=by gcongr

theorem shifted (α:I → ℝ)
    (sold:∀q,‖reading R (N:=N) (fun U=>(rows q c U).part s) u (ub.trans bc.le)-
        reading R (N:=N) (fun U=>(rows q c U).part s) b bc.le‖≤α q):
    ‖step₀‖≤∑q,‖amount q‖*(α q):=by
  unfold shift
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _=>?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (sold q) (norm_nonneg _)

end YM.Integration.WilsonOriginalTwoFlatIRSocketBoundary
end
