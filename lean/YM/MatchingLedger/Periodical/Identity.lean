import YM.MatchingLedger.Periodical.Grain

/-!
# Project to the physical summary (on the forest slice). No promise of
period-independent exceptional control by the identity alone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Periodical
open Function Filter Lattice RG Wilson Tree Pressure Pressure.Stores Precision Push.Uniform
open PatchArea Action Books MvPolynomial Gazette Set Metric MeasureTheory
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff Finset

section templates
variable {ι X : Type} [DecidableEq ι] [Fintype ι] [MeasurableSpace X] [Nonempty X]

lemma local_line (μ : Measure X) [IsProbabilityMeasure μ]{f : (ι→ X) → ℝ}(h: Envelope f)(i:ι)
    (he : ∀ U, (∫ x,f (Function.update U i x) ∂μ)=0) : (∫ x,f x ∂Measure.pi (fun _ : ι=>μ))=0:= by
  rw [integrate_window μ {i} h]; let I:= ({i} : Finset ι)
  haveI hI : Unique { x // x∈I } :=
    { default:=⟨i,Finset.mem_singleton_self _⟩
      uniq x := Subtype.ext (Finset.mem_singleton.mp x.property) }
  let C:= joinWindow (X:=X) I
  let y:=MeasurableEquiv.funUnique {x // x∈ I} X
  let a : Measure ({x // x∈ I}→ X) := Measure.pi (fun _=>μ)
  have hv := measurePreserving_funUnique μ {x// x ∈ I}
  have hu : MeasurePreserving y a μ:= by unfold a y; convert! hv using 1; congr! -- convert
  -- watch Fintype when introduce Unique local: a, etc
  have hm (u:{x // x ∉ I}→X) : (∫ x, f (C (x,u)) ∂a)=0 := by
    rw [← (hu.symm).integral_comp y.symm.measurableEmbedding]
    let v:= y.symm (Classical.arbitrary X); let x:= C (v,u)
    have hu(p): C (y.symm p,u) = Function.update x i p := by
      ext j; by_cases h:j=i
      · subst j; rw [Function.update_self, show C (y.symm p,u) i= y.symm p ⟨i,Finset.mem_singleton_self _⟩ from join_on (s:=I) _ _ (Finset.mem_singleton_self _)]; exact y.apply_symm_apply p
      have hj:j∉I:= fun hh=> h (Finset.mem_singleton.mp hh)
      rw [Function.update_of_ne h]; exact (join_off (s:=I) _ u hj).trans (join_off v u hj).symm
    change (∫ p, f (C (y.symm p,u)) ∂μ)=0
    simp_rw [hu]; exact he x
  -- may require revert a alias
  simp_rw [show ∀ u, (∫ x, f (joinWindow {i} (x,u)) ∂Measure.pi (fun _ : {x // x∈({i}:Finset ι)} => μ))=0 from hm]; simp
end templates

variable {c f : Side}{G : Gauge}{S : StepData c f} (F : Forest S.ratio) (s : S.Choices) (hB:S.patch.Branches S.kernel G)
    {A : ChartRatio G} {Y : Chip (Page G c)} {t r : ℝ} {R : Support c} (i : Needle F G) (p : Poly (Needle F G))
local notation "I" => Sum.inl i
local notation "D" => depot F (Sum.inl i)
local notation "W" => weigh (F.order G) (Cooling.weight F (runway Y) t)

section identity
variable {n : ℕ} (H : Budget G A n) (ht:0<t) (hg:0<r) (hr:r≤dial A)(hY:‖Y‖≤r)(hh:r≤ H.space S.patch S.kernel)(he:arc F (.inl i)⊆R)
include H hB ht hg hr hY hh he
lemma sprig : W (milled F s A Y t r R i p)=0 := by
  unfold weigh; rw [div_eq_zero_iff]; left
  simp_rw [mul_comm (milled F s A Y t r R i p _)] -- fill
  exact local_line G.probHaar ((Cooling.weight_pass F (runway Y) t hB).toEnvelope.mul (milled_pass F s Y t r R i p H hr hY hh)) i.1 (fun U=> exit F s hB Y U t i p H hr hY hh he ht hg)
end identity
end YM.MatchingLedger.Periodical
