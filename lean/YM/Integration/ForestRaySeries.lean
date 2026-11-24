import YM.Integration.OriginalRadialSeries
import YM.WilsonCoeffUV.Kinetic.Saddle

/-! The original radial field read of a finite sum of paid series with
their distinct explicit coupling powers and an analytic forest chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ForestRaySeries
open Function Filter Matrix PowerSeries WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo
open OriginalRadialSeries
open scoped Topology ContDiff Classical

variable {V U Y : Type} [Fintype V] [Fintype U] [Fintype Y]

structure Reads (v : Lawn V) (P : Ink V) (f : ℝ→ℝ) : Prop where
  regular : ContDiffAt ℝ ω f 0
  read : observed v P=OriginalRadialSeries.scalar f

private theorem plus {f h : ℝ→ℝ} (hf : ContDiffAt ℝ ω f 0) (hh : ContDiffAt ℝ ω h 0) :
    OriginalRadialSeries.scalar (f+h)=OriginalRadialSeries.scalar f+OriginalRadialSeries.scalar h := by
  unfold OriginalRadialSeries.scalar
  have a : Green (fun z : Lawn Unit=>f (z ())) := hf.comp 0 (by fun_prop)
  have b : Green (fun z : Lawn Unit=>h (z ())) := hh.comp 0 (by fun_prop)
  rw [←map_add,←jet_add a b]
  rfl

omit [Fintype V] in
theorem add {v : Lawn V} {P Q : Ink V} {f h : ℝ→ℝ} (a : Reads v P f) (b : Reads v Q h) :
    Reads v (P+Q) (fun t=>f t+h t) :=
  ⟨a.regular.add b.regular,by rw [map_add,a.read,b.read,←plus a.regular b.regular]; rfl⟩

omit [Fintype V] in
theorem mul {v : Lawn V} {P Q : Ink V} {f h : ℝ→ℝ} (a : Reads v P f) (b : Reads v Q h) :
    Reads v (P*Q) (fun t=>f t*h t) :=
  ⟨a.regular.mul b.regular,by rw [map_mul,a.read,b.read,←OriginalRadialSeries.mul a.regular b.regular]; rfl⟩

omit [Fintype V] in
theorem zero (v : Lawn V) : Reads v 0 (fun _=>0) := by
  refine ⟨contDiffAt_const,?_⟩
  simp [OriginalRadialSeries.scalar,observed,jet_const,realS]

omit [Fintype V] in
theorem powers (v : Lawn V) (k : ℕ) : Reads v (X^k) (fun t=>t^k) := by
  have one : Reads v 1 (fun _=>1) := ⟨contDiffAt_const,by simp [OriginalRadialSeries.scalar,observed,jet_const,realS]⟩
  have variable' : Reads v X id := ⟨contDiffAt_id,by simp [observed]⟩
  induction k with
  | zero => simpa only [pow_zero] using one
  | succ k ih => simpa only [pow_succ,id_eq] using mul ih variable'

theorem chart (θ : Lawn (U⊕V)→Lawn U) (hθ : Green θ) (h0 : θ 0=0)
    (v : Lawn (U⊕V)) (f : Lawn (U⊕V)→ℝ) (hf : Green f) :
    Reads v (retool θ (jet f)) (fun g=>f (spider θ (g • v))) := by
  have h := spider_green hθ
  have hz := spider_zero h0
  have hc : Green (f ∘ spider θ) :=
    (show ContDiffAt ℝ ω f (spider θ 0) from hz.symm ▸ hf).comp 0 h
  refine ⟨?_,?_⟩
  · change ContDiffAt ℝ ω ((f ∘ spider θ) ∘ (fun g:ℝ=>g • v)) 0
    exact ContDiffAt.comp 0 (by simpa only [zero_smul] using hc) (by fun_prop)
  rw [pivot,traveling _ h hz _ hf]
  exact restriction v _ hc

theorem linear (θ : Lawn (U⊕V)→Lawn U) (hθ : Green θ) (h0 : θ 0=0)
    (v : Lawn (U⊕V)) (D : Matrix Y (U⊕V) ℝ) (f : Lawn Y→ℝ) (hf : Green f) :
    Reads v (retool θ (loom D (jet f))) (fun g=>f (D *ᵥ spider θ (g • v))) := by
  rw [loom_jet D f hf]
  exact chart θ hθ h0 v _ (ContDiffAt.comp 0 (by rw [Matrix.mulVec_zero]; exact hf) (board D))

end YM.Integration.ForestRaySeries
end
