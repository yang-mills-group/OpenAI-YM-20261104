import YM.Integration.QLocalPhysicalPathKernel

/-! Every physical coordinate of the common chronological path has the
original Wilson scene, for all positions before the upper cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalPathMarginals
open Finset Function Preorder Set ProbabilityTheory MeasureTheory Lattice Wilson RG OPE.Therm
open QLocalPhysicalPathKernel
open scoped ENNReal Classical
variable {G : Gauge} (C : Family G) (hC : C.Makes) {N p : ℕ}
local notation "X" k => Config G (C.side k p)
local notation "stageLaw" k => scene C.path N p k
local notation "Ω" => ((k : ℕ) → Config G (C.side k p))

theorem origin : (path C hC N p).map (fun ω : Ω=>ω 0)=stageLaw 0 := by
  let e := MeasurableEquiv.piUnique (fun i : Finset.Iic 0=>X i.val)
  have headAt : (path C hC N p).map (frestrictLe 0)=(stageLaw 0).map e.symm := by
    unfold path Kernel.trajMeasure
    rw [Measure.map_comp _ _ (measurable_frestrictLe _),Kernel.traj_map_frestrictLe,
      Kernel.partialTraj_self,Measure.id_comp]
  change (path C hC N p).map (e ∘ frestrictLe 0)=stageLaw 0
  rw [←Measure.map_map e.measurable (measurable_frestrictLe _),headAt]
  exact e.map_map_symm

private theorem second {α β:Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν:Measure α) [IsProbabilityMeasure ν] (K:Kernel α β) [IsMarkovKernel K] :
    (ν ⊗ₘ K).snd=K ∘ₘ ν:=Measure.snd_compProd _ _

private theorem mapSecond {α β γ:Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (ν:Measure α) (f:α→β) (g:α→γ) (hf:Measurable f) (hg:Measurable g):
    ν.map g=(ν.map (fun x=>(f x,g x))).snd:=
  (Measure.map_map (μ:=ν) measurable_snd (hf.prodMk hg)).symm

private theorem prob {α:Type*}[MeasurableSpace α](ν:Measure α)[IsProbabilityMeasure ν]:SFinite ν:=inferInstance

theorem one {k : ℕ} (hk : k < N) :
    (path C hC N p).map (fun ω : Ω=>ω (k+1))=
      next C N p k ∘ₘ ((path C hC N p).map (fun ω : Ω=>ω k)) := by
  letI : IsProbabilityMeasure (stageLaw 0) := OPE.Therm.probability (H:=C.path) (p:=p) hC.wilson (Nat.zero_le N)
  letI : IsProbabilityMeasure (path C hC N p):=path_probability C hC N p
  let past : Measure ((i:Finset.Iic k)→X i.val):=(path C hC N p).map (frestrictLe k)
  letI : IsProbabilityMeasure past:=
    Measure.isProbabilityMeasure_map (measurable_frestrictLe k).aemeasurable
  letI : SFinite past:=prob past
  letI : IsMarkovKernel (next C N p k):=isMarkov C hC hk
  let t := fun u : (i : Finset.Iic k) → X i.val=>u ⟨k,Finset.mem_Iic.mpr le_rfl⟩
  have mt : Measurable t := measurable_pi_apply _
  have cross : steps C hC N p k=next C N p k ∘ₖ Kernel.deterministic t mt := by
    rw [Kernel.comp_deterministic_eq_comap]
    simp only [steps,hop,dif_pos hk,t]
  calc
    _ = (past ⊗ₘ steps C hC N p k).snd := by
      dsimp only [past]
      unfold path
      rw [Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure]
      exact mapSecond _ _ _ (measurable_frestrictLe k) (measurable_pi_apply _)
    _ = (steps C hC N p k) ∘ₘ past := second past _
    _ = _ := by
      dsimp only [past]
      rw [cross,←Measure.comp_assoc,Measure.deterministic_comp_eq_map mt,Measure.map_map mt (measurable_frestrictLe _)]
      rfl

theorem observed {k : ℕ} (hk : k ≤ N) :
    MeasurePreserving (fun ω : Ω=>ω k) (path C hC N p) (stageLaw k) := by
  refine ⟨measurable_pi_apply _,?_⟩
  induction k with
  | zero=>exact origin C hC
  | succ k ih=>rw [one C hC hk,ih (Nat.le_trans (Nat.le_succ _) hk),marginal C hC hk]

end YM.Integration.WilsonPositionOriginalPathMarginals
end

