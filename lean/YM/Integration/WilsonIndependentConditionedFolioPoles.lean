import YM.Integration.WilsonOlderFreshSoftSocketTotal
import YM.Integration.WilsonOriginalPublicNodalCanonical

/-! Only sockets of the submitted column's own Laurent degree can have a nonzero charge. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedFolioPoles
open Function Finset Lattice Wilson RG Source Labels Pert.Asymptotics
open PhysicalNext.Repeat.Legato ActualRunPhysicalPages WilsonThermometerDeclaredSeeds
open WilsonOriginalStarSceneWords (pole)
open WilsonReceivedCanonicalVerseBasis (dose)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonOriginalPublicNodalCanonical (request)
open WilsonOlderFreshSoftSocketMeasuredCash (ticket packet)
open WilsonOlderFreshSoftSocketRestored (degree)
open WilsonOlderFreshSoftSocketFaces (fill)
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[DecidableEq I](R:Run G)(d:I→ℕ)
local notation "F" i:max => R.family.labels.level (d i)
variable (b:(i:I)→(R.family.labels.level (d i)).Index)(N per K:ℕ)
local notation "v" => request R d b (N:=N) (p:=per) (K:=K)
local notation "τ" => (R.family.path.rep N per K).p.threshold
local notation "g" => regulatorRun R.family N per K

omit [DecidableEq I] in
theorem socket (i:I)(c:Choice R d i)
    (different:pole R d (entry R d i c)≠((F i).grades (b i)).2):
    dose R d N per K v i c=0:=by
  cases c with
  | inl u=>
    by_cases hz:b i=0
    · apply False.elim
      apply different
      rw [hz,(F i).zero_degree]
      rfl
    · change (F i).scaled τ (Pi.single (b i) 1) 0=0
      rw [Frame.scaled_apply,Pi.single_eq_of_ne (Ne.symm hz),mul_zero]
  | inr c=>
    have other:c.1≠b i:=by
      intro hc
      apply different
      change ((F i).grades c.1).2=((F i).grades (b i)).2
      rw [hc]
    have dropped:((F i).core (v i)) c.1=0:=by
      by_cases hu:c.1=0
      · simp [Frame.core,hu]
      · change Function.update ((F i).scaled τ (Pi.single (b i) 1)) 0 0 c.1=0
        rw [Function.update_of_ne hu,Frame.scaled_apply,Pi.single_eq_of_ne other,mul_zero]
    change WilsonOriginalStarLaurentWallet.coefficient R (d i) g τ ((F i).core (v i)) c=0
    rw [WilsonOriginalStarLaurentWallet.coefficient,dropped,mul_zero,zero_mul]

theorem marked (S:Finset I)(q:Selection R d S)
    (different:degree R d S (fill R d S q)≠∑i:S,((F i).grades (b i)).2):
    weight R d N per K v S q=0 ∧ ticket R d S v N per K q=0:=by
  classical
  have absent:¬∀i:S,pole R d (entry R d (i:I) (q i))=((F i).grades (b i)).2:=by
    intro same
    apply different
    rw [degree,←Finset.sum_coe_sort S]
    apply Finset.sum_congr rfl
    intro i _
    change pole R d (entry R d (i:I) (fill R d S q i))=_
    rw [show fill R d S q i=q i from dif_pos i.property]
    exact same i
  obtain ⟨i,no⟩:=not_forall.mp absent
  have zero:=socket R d b N per K i (q i) no
  constructor
  · exact Finset.prod_eq_zero (Finset.mem_univ i) zero
  · apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [zero,zero_mul]

omit [DecidableEq I] in
theorem coordinate (live:K≤N)(i:I)(j:(F i).Index):
    WilsonOriginalPublicTrialFigure.amount R d g
      (fun a=>WilsonPositionProgramReportedField.entire R (d a) K (N,per) (v a)) i j= (Pi.single (b i) (1:ℂ):(F i).Coeff) j:=by
  have hg:0<g:=ActualRunKernelPackets.regulator_pos R N per K live
  rw [WilsonOriginalPublicTrialFigure.amount,WilsonOriginalPublicNodalCanonical.ray,Frame.scaled_apply]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hg.ne']

omit [DecidableEq I] in
theorem publication (live:K≤N)(S:Finset I)(a:(i:S)→(F i).Index):
    packet R d S v N per K a=if a=fun i:S=>b (i:I) then 1 else 0:=by
  classical
  unfold packet
  simp only [coordinate R d b N per K live]
  split_ifs with hit
  · simp [hit]
  · have missed:¬∀i:S,a i=b i:=fun h=>hit (funext h)
    obtain ⟨i,m⟩:=not_forall.mp missed
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Pi.single_eq_of_ne m _)

end YM.Integration.WilsonIndependentConditionedFolioPoles
end
