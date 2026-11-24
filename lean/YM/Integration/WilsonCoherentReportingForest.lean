import YM.Integration.WilsonCoherentReportingPivot
import YM.Integration.WilsonReportingForestRelative

/-! Partial source Taylor on the actual relative Haar chart. A pivot is
shared by all the crossings of its ordered parent pair. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentReportingForest
open Function Lattice Wilson RG Tree Set Finset RG16 Precision PertExtension
open RGComparison.Core16 RGComparison.Core16.Spool PhysicalNext.Repeat.Legato
open WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots
open scoped Classical NNReal

variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (T : Forest S.ratio) (B : Finset T.Free)
local notation "E" => moving T B

def drift (X : ↥E → G.Color) (e : Edge (Site f)) : G.Color :=
  if h : e∈T.trunks then 0 else if active : (⟨e,h⟩:T.Free)∈E then X ⟨⟨e,h⟩,active⟩ else 0

theorem size (X : ↥E → G.Color) (e : Edge (Site f)) : ‖drift T B X e‖≤‖X‖ := by
  unfold drift
  split <;> rename_i h
  · simp
  · split
    · apply norm_le_pi_norm
    · simp

theorem edge (v : ({i:T.Free|i∉E}:Set T.Free) → G.El) (X : ↥E → G.Color) (t : ℝ) (e : Edge (Site f)) :
    restored T B v (Chart.expLinks G (↥E) (t • X)) e =
      G.lieExp (t • drift T B X e) * restored T B v 1 e := by
  let F := fun x : ↥E → G.El => (cut T E).symm (x*background T B v,v)
  have inside (x : ↥E → G.El) (i : ↥E) : F x i.val=x i*background T B v i :=
    congrFun (congrArg Prod.fst ((cut T E).apply_symm_apply (x*background T B v,v))) i
  have outside (x : ↥E → G.El) (i : ({i:T.Free|i∉E}:Set T.Free)) : F x i.val=v i :=
    congrFun (congrArg Prod.snd ((cut T E).apply_symm_apply (x*background T B v,v))) i
  let x := Chart.expLinks G (↥E) (t • X)
  change T.drape (F x) e = G.lieExp (t • drift T B X e) * T.drape (F 1) e
  by_cases h : e∈T.trunks
  · rw [T.on_tree (F x) ⟨e,h⟩,T.on_tree (F 1) ⟨e,h⟩]
    simp [drift,h]
  · let i : T.Free := ⟨e,h⟩
    rw [T.off_tree (F x) i,T.off_tree (F 1) i]
    by_cases hi : i∈E
    · rw [inside x ⟨i,hi⟩,inside 1 ⟨i,hi⟩]
      simp [drift,h,hi,i,x,Chart.expLinks]
    · rw [outside x ⟨i,hi⟩,outside 1 ⟨i,hi⟩]
      simp [drift,h,hi,i]

end YM.Integration.WilsonCoherentReportingForest
