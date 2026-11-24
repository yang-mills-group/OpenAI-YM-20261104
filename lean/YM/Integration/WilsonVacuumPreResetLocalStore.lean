import YM.Integration.WilsonVacuumPreResetColdInput

/-! A single genuine quiet support leaves every remote original hard partner
in the pre-reset field. An incident inventory is detected before the signed sum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetLocalStore
open Function Finset Lattice Wilson RG PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}

def outside (A:Activities G n)(J:Support n):Activities G n:=
  {A with K:=fun i=>if Disjoint (A.forced i).inventory J then A.K i else 0}

theorem charged (A:Activities G n)(B:BudgetPoint)(J:Support n)
    (b:Finset ℕ)(U:Config G n):
    (outside A J).gasOccurrence B b U=
      if Healthy B.threshold J U then A.gasOccurrence B b U else 0:=by
  by_cases eligible:A.admissible B U b
  · have whole:(outside A J).admissible B U b:=eligible
    rw [Activities.gasOccurrence,if_pos whole,Activities.gasOccurrence,if_pos eligible]
    by_cases good:Healthy B.threshold J U
    · rw [if_pos good]
      apply prod_congr rfl
      intro i hi
      have inside:(A.forced i).inventory⊆flags B.threshold U:=by
        rw [←eligible.2];intro z hz;exact Finset.mem_biUnion.mpr ⟨i,hi,hz⟩
      have pass:Disjoint (A.forced i).inventory J:=Finset.disjoint_left.mpr
        (fun _ hx hJ=>Finset.disjoint_left.mp good hJ (inside hx))
      change (if Disjoint (A.forced i).inventory J then A.K i else 0) U=A.K i U
      rw [if_pos pass]
    · rw [if_neg good]
      obtain ⟨z,hJ,hz⟩:=Finset.not_disjoint_iff.mp good
      rw [←eligible.2] at hz
      obtain ⟨i,hi,zi⟩:=Finset.mem_biUnion.mp hz
      apply Finset.prod_eq_zero hi
      change (if Disjoint (A.forced i).inventory J then A.K i else 0) U=0
      rw [if_neg (Finset.not_disjoint_iff.mpr ⟨z,zi,hJ⟩)];rfl
  · have none:¬(outside A J).admissible B U b:=eligible
    rw [Activities.gasOccurrence,if_neg none,Activities.gasOccurrence,if_neg eligible]
    simp

theorem cutoff (A:Activities G n)(B:BudgetPoint)(J:Support n)(U:Config G n):
    (outside A J).gas B U=if Healthy B.threshold J U then A.gas B U else 0:=by
  unfold Activities.gas
  simp_rw [charged]
  by_cases good:Healthy B.threshold J U
  · simp [good]
  · simp [good]

theorem paid {A:Activities G n}{B:BudgetPoint}{k:ℝ}(h:A.KBound B k)(J:Support n):
    (outside A J).KBound B k:=by
  obtain ⟨u,hu,fin⟩:=h
  refine ⟨u,fun i=>⟨(hu i).1,fun U=>?_⟩,fin⟩
  change ‖(if Disjoint (A.forced i).inventory J then A.K i else 0) U‖≤u i
  split_ifs
  · exact (hu i).2 U
  · simpa using (hu i).1

theorem original (R:Run G){N per m:ℕ}(hm:m≤N)
    (J:Support (R.family.side m per)):
    let Y:=R.family.path.rep N per m
    let Z:Rep G (R.family.side m per):={Y with activities:=outside Y.activities J}
    Z.activities.KBound Y.p (R.family.path.levels.clock.forcedAllowance m) ∧
    ∀U,Z.eval U=if Healthy Y.p.threshold J U then Y.eval U else 0:=by
  intro Y Z
  refine ⟨paid (R.makes.wilson.represents N per m hm).good.labels.boundK J,fun U=>?_⟩
  change Real.exp (Y.exponent U)*(outside Y.activities J).gas Y.p U=_
  rw [cutoff]
  split_ifs
  · rfl
  · exact mul_zero _

end YM.Integration.WilsonVacuumPreResetLocalStore
