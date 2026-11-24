import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Basis

/-! A fixed determining set in the authentic Wilson free quotient. The signed physical
station can compensate each such source by its own two actual degrees. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalVaneBasis
open Lattice Wilson Labels RG Cells Source Further.CorrectedLift
open Push.CutoffProjectors
open scoped BigOperators Classical
variable {G:Gauge}(C:Family G)(d:ℕ)

def axis (i:(C.labels.level d).Index):C.label d:=Pi.single i (1:ℂ)
def field (i:(C.labels.level d).Index):(Cells.standard C).Field d:=(Cells.standard C).project d (axis C d i)

private theorem degree {z:ℂ}{m n:ℕ}(active:z≠0)(test:Complex.ofReal ((2:ℝ)^m)*z=Complex.ofReal ((2:ℝ)^n)*z):m=n:=by
  have e:Complex.ofReal ((2:ℝ)^m)=Complex.ofReal ((2:ℝ)^n):=mul_right_cancel₀ active test
  exact (pow_right_injective₀ (a:=(2:ℝ)) (by norm_num) (by norm_num)) (Complex.ofReal_injective e)

private theorem diagonal (i:(C.labels.level d).Index)(n:(C.labels.level d).Index→ℕ):
    (fun j=>Complex.ofReal ((2:ℝ)^(n j))*(axis C d i) j)=Complex.ofReal ((2:ℝ)^(n i)) • axis C d i:=by
  funext j
  change _=Complex.ofReal ((2:ℝ)^(n i))*(axis C d i) j
  by_cases h:j=i
  · subst j;rfl
  · simp [axis,Pi.single_eq_of_ne h]

theorem pure (i:(C.labels.level d).Index):
    ∀j,(ladder C d (field C d i)) j≠0 → (C.labels.level d).grades j=(C.labels.level d).grades i:=by
  let F:=C.labels.level d
  let z:=axis C d i
  let keep:=retain F ((Cells.standard C).null d)
  have height:zoom F 2 (keep z)=Complex.ofReal ((2:ℝ)^(F.grades i).1) • keep z:=by
    calc
      _=keep (zoom F 2 z):=(free_zoom C 2 z).symm
      _=keep (Complex.ofReal ((2:ℝ)^(F.grades i).1) • z):=congrArg keep (diagonal C d i (fun k=>(F.grades k).1))
      _=_:=map_smul _ _ _
  have arity:F.scaled 2 (keep z)=Complex.ofReal ((2:ℝ)^(F.grades i).2) • keep z:=by
    calc
      _=keep (F.scaled 2 z):=(free_scaled C 2 z).symm
      _=keep (Complex.ofReal ((2:ℝ)^(F.grades i).2) • z):=congrArg keep (diagonal C d i (fun k=>(F.grades k).2))
      _=_:=map_smul _ _ _
  intro j active
  change (keep z) j≠0 at active
  apply Prod.ext
  · exact degree active (congrFun height j)
  · exact degree active (congrFun arity j)

theorem resolve (x:(Cells.standard C).Field d):
    ∑i,(ladder C d x) i • field C d i=x:=by
  let F:=C.labels.level d
  have rep:∑i,(ladder C d x) i • axis C d i=ladder C d x:=by
    funext j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp [axis]
    · intro k _ ne
      simp [axis,Pi.single_eq_of_ne (Ne.symm ne)]
    · simp
  calc
    _=(Cells.standard C).project d (∑i,(ladder C d x) i • axis C d i):=by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun i _=>(map_smul ((Cells.standard C).project d) _ _).symm)
    _=(Cells.standard C).project d (ladder C d x):=congrArg _ rep
    _=x:=ladder_reads x

end YM.Integration.WilsonPhysicalVaneBasis
