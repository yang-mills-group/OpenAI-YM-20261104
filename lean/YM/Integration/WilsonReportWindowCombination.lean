import YM.Integration.WilsonReportFittedSupport

/-! The four registered mixed Gram columns are one physical insertion.
Its incoming support does not change under the signed combination. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportWindowCombination
open Function Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Next Next.Rank Next.Rank.Spindle
open OPE OPE.Strobe OPE.Vitrines Extra.Histories Extra.Multi MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open WilsonPhysicalMarkedDefect WilsonPhysicalMarkedDefect.StoredInterior WilsonReportWindowSource
open scoped Classical BigOperators Topology
variable {G : Gauge} (C : Family G) {d k N p : ℕ}

/-- Signed combinations are deposited *before* choosing their polynomial, old regular
or forced field, covers, primary failures or their retained series. -/
theorem four (law : C.Makes) (grade : C.ref d≤k) (cut : k≤N) (c : Fin 4→ℂ) (v : Fin 4→C.label d) :
    let B := (C.path.levels.budget k).B
    let w := ∑h,c h • v h
    let Q := parcel C d k N p
    (∀u,(Q u).support=(Q 0).support) ∧
    (Q w).x=∑h,c h • (Q (v h)).x ∧
    (Q w).regular=∑h,c h • (Q (v h)).regular ∧
    (Q w).forced=∑h,c h • (Q (v h)).forced ∧
    ∀ x U, opened C (N:=N) w x U=∑h,c h*opened C (N:=N) (v h) x U ∧
      alarm C (N:=N) w x U=∑h,c h*alarm C (N:=N) (v h) x U ∧
      bead C d k N p B w x U=∑h,c h*bead C d k N p B (v h) x U := by
  let w := ∑h,c h • v h
  let T := C.factory d N p
  let Q := parcel C d k N p
  let A := C.path.rep N p k
  let B := (C.path.levels.budget k).B
  let α := alto C.path k d
  have dims := (law.calibrated d N p (grade.trans cut)).linear k grade cut
  have support (u : C.label d) : (Q u).support=(Q 0).support := by
    simpa only [Q,parcel,map_zero] using dims.2.2.2 (T.terminal.symm u)
  let X := (IsLinearMap.mk' _ dims.1).comp T.terminal.symm.toLinearMap
  let S := (IsLinearMap.mk' _ dims.2.1).comp T.terminal.symm.toLinearMap
  let H := (IsLinearMap.mk' _ dims.2.2.1).comp T.terminal.symm.toLinearMap
  have coords : (Q w).x=∑h,c h • (Q (v h)).x := by
    change X w=∑h,c h • X (v h)
    simp only [w,map_sum,map_smul]
  have regs : (Q w).regular=∑h,c h • (Q (v h)).regular := by
    change S w=∑h,c h • S (v h)
    simp only [w,map_sum,map_smul]
  have forces : (Q w).forced=∑h,c h • (Q (v h)).forced := by
    change H w=∑h,c h • H (v h)
    simp only [w,map_sum,map_smul]
  refine ⟨support,coords,regs,forces,?_⟩
  intro x U
  let Z := pull 1 x U
  have coord0 : (Q w).x 0=∑h,c h*(Q (v h)).x 0 := by
    rw [coords]; simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  have coeffs (j : (C.labels.level d).Index) :
      amplitude C N p d k (Q w) j=∑h,c h*amplitude C N p d k (Q (v h)) j := by
    unfold amplitude
    rw [coords]
    simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  have values : fitted C N p d k (Q w) Z=∑h,c h*fitted C N p d k (Q (v h)) Z := by
    simp only [fitted,coeffs,sum_mul,mul_sum,mul_assoc]
    rw [sum_comm]
  have reg (i : ℕ) : (Q w).regular i Z=∑h,c h*(Q (v h)).regular i Z := by
    rw [regs]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  have row (u : C.label d) (i : ℕ) :
      retained C (N:=N) u i x U =
        if coverNumber A.p.B ((Q 0).support i)<B ∧ Healthy A.p.threshold ((Q 0).support i) Z then
          α*(Q u).regular i Z else 0 := by
    change (if coverNumber A.p.B ((Q u).support i)<B then
      α*masked A.p.threshold ((Q u).support i) ((Q u).regular i) Z else 0)=_
    rw [support u]
    by_cases small : coverNumber A.p.B ((Q 0).support i)<B
    · by_cases live : Healthy A.p.threshold ((Q 0).support i) Z
      · simp [small,live]
      simp [small,live]
    simp [small]
  have rows (i : ℕ) : retained C (N:=N) w i x U=∑h,c h*retained C (N:=N) (v h) i x U := by
    simp_rw [row]
    split_ifs
    · rw [reg,mul_sum]
      apply sum_congr rfl
      intro h _
      ring
    simp
  have summable (h : Fin 4) : Summable (fun i=>c h*retained C (N:=N) (v h) i x U) := by
    obtain ⟨a,_,hs,_,dom⟩ := (WilsonReportWindowSource.actual C law grade cut (v h)).2.2.1
    exact (hs.of_norm_bounded (fun i=>dom i x U)).mul_left _
  have series : (∑'i,retained C (N:=N) w i x U)=∑h,c h*(∑'i,retained C (N:=N) (v h) i x U) := by
    simp_rw [rows]
    rw [Summable.tsum_finsetSum (fun h _=>summable h)]
    simp_rw [tsum_mul_left]
  have op : opened C (N:=N) w x U=∑h,c h*opened C (N:=N) (v h) x U := by
    change α*((Q w).x 0+fitted C N p d k (Q w) Z)+(∑'i,retained C (N:=N) w i x U)=
      ∑h,c h*(α*((Q (v h)).x 0+fitted C N p d k (Q (v h)) Z)+(∑'i,retained C (N:=N) (v h) i x U))
    rw [coord0,values,series]
    simp only [mul_add,mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro h _
    ring
  have failedField : alarm C (N:=N) w x U=∑h,c h*alarm C (N:=N) (v h) x U := by
    change α*(if Healthy A.p.threshold ((C.localSection d).footprint 0) Z then 0 else -fitted C N p d k (Q w) Z)=
      ∑h,c h*(α*(if Healthy A.p.threshold ((C.localSection d).footprint 0) Z then 0 else -fitted C N p d k (Q (v h)) Z))
    split_ifs
    · simp
    rw [values]
    simp only [mul_neg,mul_sum,Finset.sum_neg_distrib]
    congr 1
    apply sum_congr rfl
    intro h _
    ring
  refine ⟨op,failedField,?_⟩
  simp_rw [fun b=>(WilsonReportWindowSource.actual C law grade cut b).2.2.2 x U]
  rw [op,failedField,←sum_add_distrib]
  simp only [mul_add]

end YM.Integration.WilsonReportWindowCombination
end

