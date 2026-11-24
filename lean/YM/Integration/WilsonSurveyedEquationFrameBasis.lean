import YM.Integration.WilsonSurveyedEquationFrameOrbit

/-! A full finite classical field section made from the prescribed survey on
physical directions and the actually integrated order-independent Wilson
equation marks on its complement. Both summands are evaluated on group links. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace YM.Integration.WilsonSurveyedEquationFrameBasis

open Lattice RG Wilson Labels Source Maxwell Maxwell.Free Push Push.Mark XSpace
open Function MvPolynomial
open scoped Classical BigOperators

variable {G : Gauge} {d : ℕ}

def projection : Label G d →ₗ[ℂ] Label G d :=
  On.sectionMap d ∘ₗ (observable G d).rangeRestrict

def kernel : Label G d →ₗ[ℂ] Label G d := LinearMap.id - projection

theorem equation (p : Label G d) : kernel p ∈ equationIdeal G d := by
  apply LinearMap.mem_ker.mpr
  rw [kernel, LinearMap.sub_apply, LinearMap.id_apply, projection, LinearMap.comp_apply, map_sub,On.recovers]
  exact sub_self _

theorem graded {m : ℕ × ℕ} {p : Label G d} (hp : p ∈ Labels.Grade m) :
    projection p ∈ Labels.Grade m := by
  obtain ⟨a,b⟩ := m
  apply On.section_grade
  change IsWeightedHomogeneous bwt (reduceEq p.val) (a,b)
  have hh : IsWeightedHomogeneous bidegree p.val (a,b) := (pure_grade ..).mp hp
  have he := commuting bidegree bwt (reduceEq (G:=G)) (reduce_grade (fun i => (i+2,(1:ℕ)))) p.val (a,b)
  rw [hh.weightedHomogeneousComponent_same] at he
  rw [←he]
  exact weightedHomogeneousComponent_mem ..

variable (F : Labels.Frame G d) (H : Hol G) (S : SectionData F)

def read : Label G d →ₗ[ℂ] Pre G := (S.eval_linear.mk' _).comp F.coords.toLinearMap

private theorem offered (hs : S.Sound H) (live : Bid.pop S) {m : ℕ×ℕ} {p : Label G d}
    (grade : p ∈ Labels.Grade m) : Offered H d m p (p,read F S p) := by
  refine ⟨grade,hs.gaugeInvariant _,?_,(Forms.seats (H:=H) p _).2 ?_,?_⟩
  · simp
  · have ht := hs.projects (F.coords p)
    rw [LinearEquiv.symm_apply_apply] at ht
    exact ht
  change read F S p ∈ powered G m.2
  rw [←F.basis.sum_repr p,map_sum]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : F.grades i = m
  · obtain ⟨b,B,hr,P,hP,spelling⟩ := live i
    have agree : read F S (F.basis i) = spelledPose B P := by
      change S.evaluate (F.coords (F.basis i)) = _
      rw [F.coords_basis]; exact hP
    rw [map_smul,agree,←hi]
    exact Submodule.smul_mem _ _ (pose_power B P spelling)
  rw [show F.basis.repr p i=0 from F.power_coefficient i (Ne.symm hi) grade,zero_smul,map_zero]
  exact Submodule.zero_mem _

def mixed (J : Switch G d) : Switch G d :=
  (LinearMap.id.prod (read F S)).comp projection + J.comp kernel

private theorem mixed_apply (J : Switch G d) (p : Label G d) :
    mixed F S J p = (projection p,read F S (projection p)) + J (kernel p) := rfl

private theorem proj_null {p : Label G d} (null : p ∈ equationIdeal G d) : projection p = 0 := by
  have hn : (observable G d).rangeRestrict p = 0 := Subtype.ext (LinearMap.mem_ker.mp null)
  exact (congrArg (fun x : shellSector G d => On.sectionMap d x) hn).trans (map_zero _)

private theorem proj_unit : projection (unit G d) = unit G d := by
  apply Subtype.ext
  rw [projection,LinearMap.comp_apply,On.section_value]
  change On.lifting (reduceEq (1 : Labels.Pol G))=1
  rw [map_one,map_one]

theorem complete (J : Switch G d) (issued : Campaign H d J) (sound : S.Sound H) (live : Bid.pop S) :
    Campaign H d (mixed F S J) := by
  constructor
  · intro m hm p hp
    have pp := graded hp
    have kp : kernel p ∈ Labels.Grade m := Submodule.sub_mem _ hp pp
    have a := offered F H S sound live pp
    have b := issued.each m hm (kernel p) kp
    have split : projection p + kernel p = p := by
      change projection p + (p - projection p) = p
      abel
    refine ⟨?_,?_⟩
    · have c := a.add b.takes
      rw [split] at c
      rw [mixed_apply]
      exact c
    · intro null
      have zero := proj_null null
      rw [mixed_apply,Prod.snd_add,zero]
      change Micro (read F S 0 + (J (kernel p)).2)
      rw [map_zero,zero_add]
      exact b.exacts (equation p)
  · have one := proj_unit (G:=G) (d:=d)
    have gone : kernel (unit G d)=0 := by change unit G d - projection (unit G d)=0; rw [one,sub_self]
    rw [mixed_apply,one,gone,map_zero,add_zero]
    change (unit G d,S.evaluate (F.coords (unit G d)))=_
    rw [F.coords_unit,sound.unit]

/-- Invert exactly the finite section containing these surveyed physical pivots
and actual null cylinders. The inverse has a fixed finite operator norm. -/
theorem original (W : Initialize G) :
    ∃ (J : Switch G d) (V : SectionData F) (A : Label G d ≃ₗ[ℂ] Label G d)
      (P : Label G d ≃ₗ[ℂ] Label G d) (C : ℝ), 0 ≤ C ∧
      Portfolio W.hol V A ∧ (∀ p, V.evaluate (F.coords (A p)) = reel J p) ∧
      (∀ p, P p = projection p + A (kernel p)) ∧
      (∀ p, ‖F.coords (P.symm p)‖ ≤ C * ‖F.coords p‖) := by
  obtain ⟨J₀,ext⟩ := unsym W.hol d
  let h := impression ext
  let J := h.toCampaign
  obtain ⟨V,bank,actual⟩ := weaveBuild h F
  obtain ⟨T,given⟩ := (W.surveys d).prepares F
  let P := twist (complete F W.hol T _ J given.1 given.2.1)
  let D := ((F.coords.symm.trans P.symm).trans F.coords).toLinearMap.toContinuousLinearMap
  refine ⟨_,V,_,P,‖D‖,norm_nonneg _,bank,actual,?_,?_⟩
  · intro p; rfl
  · intro p
    have bound := D.le_opNorm (F.coords p)
    simpa [D] using bound

end YM.Integration.WilsonSurveyedEquationFrameBasis
