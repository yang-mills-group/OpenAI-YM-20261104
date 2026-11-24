import YM.Integration.WilsonNormalizedReflectedForm
import YM.Integration.WilsonThermometerWeakCornerRows

/-! The two-point price on the original fitted fields, with literal units
in every inactive place. The quoted number precedes radii and proper faces. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakCornerSalary
open Function Finset Filter Set Extraction Table Spec GapsContact Ascent Frontier6 Trace.Pilot
open GapsContact.Seams PhysicalNext.Repeat.Legato PhysMS OPE OPE.Levy Push.FiniteDetection.Free
open Climb Maxwell XSpace XSpace.Normalize
open WilsonPositionReflectedTubeInputs
open scoped Classical Topology BigOperators Matrix

variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)

theorem unit (d:ℕ)(r:ℝ)(hr:0<r):cost F d r (S.unit d)=1:=by
  have X:=Work.A05.smul_conf hr detectors_in
  have v: ![S.unit d,S.unit d] = (fun _:Fin 2=>S.project d (R.family.refUnit d)):=by
    funext i
    fin_cases i <;> rfl
  have H:S.Basic:=(hierarchy F none).laws
  have faces : S.read (r • detectors) (fun _:Fin 2=> R.family.book.one d)=1:=by
    have pair : (fun _:Fin 2=> R.family.book.one d)=Fin.cons (R.family.book.one d) (fun _:Fin 1=>R.family.book.one d):=by
      funext i
      fin_cases i <;> rfl
    have single : (fun _:Fin 1=> R.family.book.one d)=Fin.cons (R.family.book.one d) (fun _:Fin 0=>R.family.book.one d):=by
      funext i
      fin_cases i
      rfl
    rw [pair,H.unital X d _,single,H.unital (Trace.valid_one _) d _]
    exact H.trivial _ _
  have bill:valTwo S d (r • detectors) (S.unit d) (S.unit d)=1:=by
    unfold valTwo
    rw [v,S.class_agrees S H.toSymmetric (respects F none) (fun _:Fin 2=>d) X]
    exact faces
  rw [cost]
  simp only [flipField,Table.conj_unit,Table.mirror_unit,bill,norm_one,Real.sqrt_one]

theorem original {n:ℕ}(J:ℝ→tower S)(V:Store G)(lead:Leading F J)
    (d:Fin n→ℕ){T:ℝ}(t:0≤T):
    ∃B:ℝ,1≤B ∧ ∀ᶠ r in trail,∀(s:Finset (Fin n))(b:Bool)(v:∀i,RG17.Free R.family (d i)),
      (∀i,‖v i‖≤T) → billSlots F r (fun i=>
         if i∈s then ⟨d i,WilsonNormalizedReflectedForm.field F J V b (d i) r (v i)⟩ else ⟨d i,S.unit (d i)⟩)≤B:=by
  choose B hp price using fun i:Fin n=>WilsonNormalizedReflectedForm.uniform F J V lead (d i) t
  refine ⟨∏ i,max 1 (B i),Finset.one_le_prod (fun i _=>le_max_left ..),?_⟩
  filter_upwards [Filter.eventually_all.mpr price,self_mem_nhdsWithin] with r h hr
  intro s b v hv
  unfold billSlots
  apply Finset.prod_le_prod
  · intro i _
    exact Real.sqrt_nonneg _
  intro i _
  let t₁:S.Tag:=⟨d i,WilsonNormalizedReflectedForm.field F J V b (d i) r (v i)⟩
  let t₀:S.Tag:=⟨d i,S.unit (d i)⟩
  let τ:=if i∈s then t₁ else t₀
  change cost F τ.1 r τ.2 ≤ max 1 (B i)
  by_cases hi:i∈s
  · have eq:τ=t₁:=if_pos hi
    rw [eq]
    exact (h i b (v i) (hv i)).trans (le_max_right ..)
  · have eq:τ=t₀:=if_neg hi
    rw [eq]
    exact (unit F (d i) r hr).le.trans (le_max_left ..)

end YM.Integration.WilsonThermometerWeakCornerSalary
end
