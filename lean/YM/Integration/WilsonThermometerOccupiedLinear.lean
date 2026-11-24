import YM.Integration.WilsonThermometerUnitFilingRawSum
import YM.Integration.WilsonThermometerMixedVacuumReading
import YM.Integration.WilsonThermometerOccupiedInterpolation

/-! The four amplitudes retain the same conditional Wilson law at every older date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerOccupiedLinear
open Function Filter Finset MeasureTheory Lattice RG Wilson Labels Source Work.G08 Next.Foundations
open Extra.Histories Extra.Histories.Relay MergeProof MergeProof.Accent Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Legato RG16 WilsonThermometerUnitFilingCoarse
open Marker WilsonThermometerOccupiedInterpolation
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N p b j:ℕ}
local notation "H" => R.family.path
local notation "X" => Config G (R.family.side b p)
local notation "J" => Stock.census (Fin 3)

def weight (q:ℝ)(i:Fin 4):ℂ:=
  if i=0 then 1-(w₁ q:ℂ)-(w₂ q:ℂ)-(w₃ q:ℂ)
  else if i=1 then w₁ q else if i=2 then w₂ q else w₃ q

theorem total (q:ℝ): ∑i:Fin 4,weight q i=1:=by
  simp [Fin.sum_univ_four,weight];ring

theorem expression {A:Type*}[AddCommGroup A][Module ℂ A] (q:ℝ)(y:Fin 4→A):
    (∑i:Fin 4,weight q i • y i)=fitted q (y 0) (y 1) (y 2) (y 3):=by
  simp [Fin.sum_univ_four,weight,fitted,sub_smul,smul_sub]
  abel

theorem shift {A:Type*}[AddCommGroup A][Module ℂ A] (q:ℝ)(y:Fin 4→A)(d:A):
    fitted q (y 0-d) (y 1-d) (y 2-d) (y 3-d)=fitted q (y 0) (y 1) (y 2) (y 3)-d:=by
  simp only [fitted,sub_sub_sub_cancel_right]
  abel

private theorem plus (f g:X→ℂ) (hf:Integrable f (prior G _))(hg:Integrable g (prior G _))(jb:j≤b):
    gust H N p b (f+g) j jb=gust H N p b f j jb+gust H N p b g j jb:=by
  induction jb using Nat.decreasingInduction with
  | self=>rw [gust_base,gust_base,gust_base]
  | of_succ i ix ih=>
    rw [gust_step H N p b _ ix,ih,StepData.push_add ((H).levels.transition_mass ..) _ _
      (gust_live H N p b f hf ix) (gust_live H N p b g hg ix),
      ←gust_step H N p b f ix,←gust_step H N p b g ix]

private theorem scale (c:ℂ) (f:X→ℂ)(hf:Integrable f (prior G _))(jb:j≤b):
    gust H N p b (c • f) j jb=c • gust H N p b f j jb:=by
  induction jb using Nat.decreasingInduction with
  | self=>rw [gust_base,gust_base]
  | of_succ i ix ih=>
    rw [gust_step H N p b _ ix,ih,StepData.push_smul _ _ _ _ (gust_live H N p b f hf ix),
      ←gust_step H N p b f ix]

private theorem summed {V:Type*} (s:Finset V)(a:V→ℂ)(f:V→X→ℂ)
    (live:∀v,Integrable (f v) (prior G _))(jb:j≤b):
    Integrable (∑i∈s,a i • f i) (prior G _) ∧
    gust H N p b (∑i∈s,a i • f i) j jb=∑i∈s,a i • gust H N p b (f i) j jb:=by
  induction s using Finset.induction_on with
  | empty=>
    simp only [sum_empty]
    have z:=scale R (N:=N) 0 (0:X→ℂ) (integrable_zero ..) jb
    exact ⟨integrable_zero ..,by simpa only [zero_smul] using z⟩
  | @insert v t hv ih=>
    simp only [sum_insert hv]
    have sc:=(live v).smul (a v)
    exact ⟨sc.add ih.1,by rw [plus R _ _ sc ih.1 jb,scale R _ _ (live v) jb,ih.2]⟩

private theorem projected (F:X→Poly (J))(paid:Integrable F (prior G _))(s:(J).Mode){j:ℕ}(jb:j ≤ b):
    (fun W=>(gust H N p b F j jb W).part s)=gust H N p b (fun U=>(F U).part s) j jb:=by
  induction jb using Nat.decreasingInduction with
  | self=>rw [gust_base,gust_base]
  | of_succ j jt ih=>
    rw [gust_step H N p b F jt,gust_step H N p b _ jt]
    have pass:=push_get ((H).levels.transition_mass j p ((H).β N p (j+1)))
      (gust_live H N p b F paid jt) s
    exact pass.trans (congrArg (((H).levels.clock.op j p).push ((H).β N p (j+1))) ih)


theorem transferred (q:ℝ)(Y:X→Poly (J))(F:Fin 4→X→Poly (J))
    (yp:Integrable Y (prior G _))(paid:∀v,Integrable (F v) (prior G _))
    (same:∀U,Y U=fitted q (F 0 U) (F 1 U) (F 2 U) (F 3 U))(jb:j≤b)(W:Config G (R.family.side j p)):
    gust H N p b Y j jb W=fitted q (gust H N p b (F 0) j jb W)
      (gust H N p b (F 1) j jb W) (gust H N p b (F 2) j jb W) (gust H N p b (F 3) j jb W):=by
  ext1 s
  let fields (v:Fin 4):X→ℂ:=fun U=>(F v U).part s
  have live(v:Fin 4):Integrable (fields v) (prior G _):=(Poly.get s).integrable_comp (paid v)
  have row:(fun U=>(Y U).part s)=∑v:Fin 4,weight q v • fields v:=by
    funext U
    rw [same,Finset.sum_apply]
    exact (expression q (fun v=>(F v U).part s)).symm
  have source:=congrFun (projected R (N:=N) Y yp s jb) W
  rw [row,(summed R Finset.univ (weight q) fields live jb).2,Finset.sum_apply] at source
  apply source.trans
  calc
    _ = ∑v:Fin 4,weight q v • (gust H N p b (F v) j jb W).part s:=by
      refine sum_congr rfl fun v _=>?_
      exact congrArg (fun z:ℂ=>weight q v • z) (congrFun (projected R (N:=N) (F v) (paid v) s jb) W).symm
    _ = _ :=expression q (fun v=>(gust H N p b (F v) j jb W).part s)

def observer (c:(J).Mode→ℂ): Poly (J) →ₗ[ℂ] ℂ where
  toFun := WilsonGeometricSignedCapture.take c
  map_add' := by intro x y; simp [WilsonGeometricSignedCapture.take,mul_add,Finset.sum_add_distrib]
  map_smul' := by intro a x; simp [WilsonGeometricSignedCapture.take,Poly.part_smul,Finset.mul_sum,mul_left_comm]

theorem observed (q:ℝ)(c:(J).Mode→ℂ)(y:Fin 4→Poly (J)):
    WilsonGeometricSignedCapture.take c (fitted q (y 0) (y 1) (y 2) (y 3))=
      fitted q (WilsonGeometricSignedCapture.take c (y 0)) (WilsonGeometricSignedCapture.take c (y 1))
        (WilsonGeometricSignedCapture.take c (y 2)) (WilsonGeometricSignedCapture.take c (y 3)):=by
  change observer c _=fitted q (observer c _) (observer c _) (observer c _) (observer c _)
  simp only [fitted,map_add,map_sub,map_smul]

theorem earlier (q:ℝ)(Y:X→ℂ)(F:Fin 4→X→ℂ)(paid:∀v,Integrable (F v) (prior G _))
    (same:∀U,Y U=fitted q (F 0 U) (F 1 U) (F 2 U) (F 3 U))(jb:j≤b):
    reading R (N:=N) Y j jb=fitted q (reading R (N:=N) (F 0) j jb)
      (reading R (N:=N) (F 1) j jb) (reading R (N:=N) (F 2) j jb) (reading R (N:=N) (F 3) j jb):=by
  have row:Y=∑v:Fin 4,weight q v • F v:=by
    funext U; rw [same,Finset.sum_apply]
    exact (expression q (fun v=>F v U)).symm
  rw [row,(WilsonThermometerUnitFilingRawSum.family R Finset.univ (weight q) F paid jb).2]
  exact expression q fun v=>reading R (N:=N) (F v) j jb

end YM.Integration.WilsonThermometerOccupiedLinear
