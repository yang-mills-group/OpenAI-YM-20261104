import YM.Integration.WilsonThermometerUnitFilingRaw

/-! Signed cell coefficients stay outside the original conditional normalization. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingRawSum
open Function Filter Finset MeasureTheory Lattice RG Wilson Labels Source Work.G08 Next.Foundations
open Extra.Histories Extra.Histories.Relay MergeProof MergeProof.Accent Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Legato RG16 WilsonThermometerUnitFilingCoarse
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N p b j:ℕ}
local notation "H" => R.family.path
local notation "X" => Config G (R.family.side b p)

theorem scaled (c:ℂ) (f:X→ℂ) (hf:Integrable f (prior G _)) (jb:j≤b):
    reading R (N:=N) (c • f) j jb=c*reading R (N:=N) f j jb:=by
  have push:gust H N p b (c • f) j jb=c • gust H N p b f j jb:=by
    induction jb using Nat.decreasingInduction with
    | self=>rw [gust_base,gust_base]
    | of_succ i ix ih=>
      rw [gust_step H N p b _ ix,ih,StepData.push_smul _ _ _ _ (gust_live H N p b f hf ix),
        ←gust_step H N p b f ix]
  unfold reading
  rw [push,Pi.smul_apply,smul_eq_mul];ring

theorem family {ι:Type*} (s:Finset ι) (a:ι→ℂ) (f:ι→X→ℂ) (paid:∀z,Integrable (f z) (prior G _)) (jb:j≤b):
    Integrable (∑z∈s,a z • f z) (prior G _) ∧
      reading R (N:=N) (∑z∈s,a z • f z) j jb=∑z∈s,a z*reading R (N:=N) (f z) j jb:=by
  classical
  induction s using Finset.induction_on with
  | empty=>
    simp only [sum_empty]
    have zero:=scaled R (N:=N) 0 (0:X→ℂ) (integrable_zero ..) jb
    exact ⟨integrable_zero ..,by simpa only [zero_smul,zero_mul] using zero⟩
  | @insert z rest outside ih=>
    simp only [sum_insert outside]
    have first:= (paid z).smul (a z)
    exact ⟨first.add ih.1,by rw [WilsonThermometerUnitFilingRaw.add R _ _ first ih.1 jb,scaled R _ _ (paid z) jb,ih.2]⟩

end YM.Integration.WilsonThermometerUnitFilingRawSum
