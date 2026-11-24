import YM.Integration.WilsonReportingPrescribedOldAction

/-! The original square action and the compensated grade-four spectator have a
finite signed assignment of original physical labels before any cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldFreeArms
open Function Set Filter MeasureTheory Lattice Wilson RG Tree Precision Source Labels
open PhysicalNext.Repeat.Legato RGComparison.Core16 RG17 Extraction Table Spec Climb
open MS MS.Local.Physical MS.Theater MS.Land MS.Menus Maxwell Maxwell.Free StressFlux Trace
open UVNext.FreeStress Trace.Pilot PhysMS OPE OPE.Therm
open WilsonReportingPrescribedOldAction WilsonInvariantActionSpectatorPrices
open private allowed tape_degree from YM.Integration.WilsonReportingPrescribedOldAction
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (B:Deck G)

abbrev Stock := ℂ × (B.BIndex (4:ℤ) 2 → ℂ)

def primary (i:B.BIndex (4:ℤ) 2) : RG17.Free R.family 4 :=
  UVNext.FreeStress.embed R.family.labels 4 (ActualOriginalDictionary.filmLabel B 4 2 i)

def booking : Stock B →ₗ[ℂ] RG17.Free R.family 4 where
  toFun z := z.1 • (Bel R.family.book).unit 4+∑i,z.2 i • primary R B i
  map_add' x y := by simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply,add_smul,Finset.sum_add_distrib];abel
  map_smul' t x := by
    simp only [Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,
      smul_add,Finset.smul_sum,smul_smul]

private theorem quotient {p q:Labels.Label G 4} (red:reduceEq p.val=reduceEq q.val) :
    UVNext.FreeStress.embed R.family.labels 4 p=UVNext.FreeStress.embed R.family.labels 4 q := by
  apply sub_eq_zero.mp
  rw [←map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (projectionExact R.family.labels).mp
  let z := (R.family.labels.level 4).coords (p-q)
  have vanish : snap R.family.labels 4 z=0 := by
    apply Subtype.ext
    change observable G 4 ((R.family.labels.level 4).coords.symm z)=0
    rw [show (R.family.labels.level 4).coords.symm z=p-q from LinearEquiv.symm_apply_apply ..,map_sub]
    exact sub_eq_zero.mpr red
  change snap R.family.labels 4 z ∈ Maxwell.residual G 4
  rw [vanish]
  exact Submodule.zero_mem _

private theorem inBasis (p:Labels.Label G 4) (film:p.val∈Film0 G 4 2) :
    ∃z:B.BIndex (4:ℤ) 2 → ℝ,
      UVNext.FreeStress.embed R.family.labels 4 p=∑i,(z i:ℂ) • primary R B i := by
  let raw : Film0 G 4 2 := ⟨p.val,film⟩
  let y : IvSpace G 4 2 := ⟨stageM G 4 2 raw,⟨raw,rfl⟩⟩
  let z := fun i=>(Indigo B 4 2).repr y i
  have fee := congrArg Subtype.val ((Indigo B 4 2).sum_repr y)
  have lamps (i:B.BIndex (4:ℤ) 2) : (Indigo B 4 2 i).val=reduceEq (MS.Theater.film B i (h:=4)) :=
    (letS B (⟨4,by decide⟩:Fin 5) (⟨2,by decide⟩:Fin 5) i).symm
  simp only [Submodule.coe_sum,SetLike.val_smul,lamps] at fee
  let q : Labels.Label G 4 := ∑i,(z i:ℂ) • ActualOriginalDictionary.filmLabel B 4 2 i
  refine ⟨z,?_⟩
  calc
    _ = UVNext.FreeStress.embed R.family.labels 4 q := by
      apply quotient R
      change reduceEq p.val=reduceEq (∑i,(z i:ℂ) • ActualOriginalDictionary.filmLabel B 4 2 i).val
      rw [Submodule.coe_sum,map_sum]
      change reduceEq p.val=∑i,reduceEq ((z i:ℂ) • MS.Theater.film B i (h:=4))
      simp only [Algebra.smul_def,map_mul,AlgHom.commutes]
      simpa only [←Algebra.smul_def,Complex.coe_smul] using! fee.symm
    _ = _ := by simp [q,primary]

theorem action : stepField R.family=∑i,(weights B i:ℂ) • primary R B i := by
  let q : Labels.Label G 4 := ∑i,(weights B i:ℂ) • ActualOriginalDictionary.filmLabel B 4 2 i
  have h : UVNext.FreeStress.embed R.family.labels 4 (square4 G)=UVNext.FreeStress.embed R.family.labels 4 q := by
    apply quotient R
    change reduceEq (square4 G).val=reduceEq (∑i,(weights B i:ℂ) • ActualOriginalDictionary.filmLabel B 4 2 i).val
    rw [Submodule.coe_sum,map_sum]
    change reduceEq (square4 G).val=∑i,reduceEq ((weights B i:ℂ) • MS.Theater.film B i (h:=4))
    simp only [Algebra.smul_def,map_mul,AlgHom.commutes]
    simpa only [←Algebra.smul_def,Complex.coe_smul] using! WilsonReportingPrescribedOldAction.reduced B
  change UVNext.FreeStress.embed R.family.labels 4 (square4 G)=_
  rw [h]
  simp [q,primary]

theorem onto (hg:G.Simple) : Surjective (booking R B) := by
  intro v
  obtain ⟨p,rfl⟩ := UVNext.FreeStress.covers R.family.labels (d:=4) v
  obtain ⟨c,t,hp⟩ := span_four hg p
  change UVNext.FreeStress.embed R.family.labels 4 p∈LinearMap.range (booking R B)
  rw [hp,map_add,map_smul,map_sum,UVNext.FreeStress.pin_unit]
  apply Submodule.add_mem
  · apply Submodule.smul_mem
    refine ⟨(1,0),?_⟩
    simp [booking]
  · apply Submodule.sum_mem
    intro a _
    rw [map_sum]
    apply Submodule.sum_mem
    intro b _
    rw [map_smul]
    apply Submodule.smul_mem
    have film : (bond (G:=G) a b (d:=4) le_rfl).val∈Film0 G 4 2 := (cinema _).mpr
      ⟨tape_degree a b,(bond (G:=G) a b (d:=4) le_rfl).property.2,
        congrArg Subtype.val (bond_real (G:=G) a b (d:=4) le_rfl)⟩
    obtain ⟨z,h⟩ := inBasis R B (bond a b (d:=4) le_rfl) film
    refine ⟨(0,fun i=>(z i:ℂ)),?_⟩
    simpa [booking] using h.symm

def assignment (hg:G.Simple) : RG17.Free R.family 4 →ₗ[ℂ] Stock B :=
  (LinearMap.exists_rightInverse_of_surjective (booking R B) (LinearMap.range_eq_top.mpr (onto R B hg))).choose

theorem assigned (hg:G.Simple) (v:RG17.Free R.family 4) : booking R B (assignment R B hg v)=v :=
  DFunLike.congr_fun (LinearMap.exists_rightInverse_of_surjective (booking R B)
    (LinearMap.range_eq_top.mpr (onto R B hg))).choose_spec v

end YM.Integration.WilsonReportingPrescribedOldFreeArms
