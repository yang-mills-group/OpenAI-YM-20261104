import YM.Integration.WilsonMeasuredRankedPrimaryBudget

/-! Extract the measured Taylor coordinate of an already counted signed
source on its actual coarse representation. Its entire regular and forced
lists remain in the projection-null remainder. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredSectionCorrection
open Filter Lattice Wilson RG Source Labels Next.Foundations
open ProjectorNext.Equivariance Trace.Physical Trace.Physical.Germ Push.Local
open scoped Classical BigOperators Topology
variable {G:Gauge} {n:Side} {d:ℕ} (F:Frame G d) (Y:Hol G) (S:SectionData F)
  (o:Site n) (W:Rep G n) (P:Coefficient F n)

def subtract (α:F.Coeff) : Coefficient F n := {P with x:=P.x-α}

def sectionValue (α:F.Coeff) (U:Config G n) : ℂ :=
  α 0 + RG.masked W.p.threshold (S.footprint o)
    (S.places (F.scaled W.p.threshold⁻¹ (F.core α)) o) U

theorem all_fields (α:F.Coeff) (U:Config G n) :
    P.density o S W U = (subtract F P α).density o S W U + (W.eval U:ℂ)*sectionValue F S o W α U := by
  have masked :
      RG.masked W.p.threshold (S.footprint o) (S.places (F.scaled W.p.threshold⁻¹ (F.core (P.x-α))) o) U =
      RG.masked W.p.threshold (S.footprint o) (S.places (F.scaled W.p.threshold⁻¹ (F.core P.x)) o) U -
      RG.masked W.p.threshold (S.footprint o) (S.places (F.scaled W.p.threshold⁻¹ (F.core α)) o) U := by
    classical
    by_cases h:Healthy W.p.threshold (S.footprint o) U
    · simp only [RG.masked,Set.indicator_of_mem (show U∈{X|Healthy W.p.threshold (S.footprint o) X} from h),
        SectionData.places,SectionData.evaluate,map_sub]
    · simp [RG.masked,h]
  have same:(subtract F P α).marked W=P.marked W:=rfl
  unfold Coefficient.density Coefficient.exponentialEntry sectionValue
  rw [same]
  change _ = (W.eval U:ℂ)*((P.x-α) 0 + _+∑'i,P.maskedTerm W i U)+_+_
  simp only [subtract] at *
  rw [masked,Pi.sub_apply]
  ring

local notation "π₁" => projection F Y W.p.threshold o P
local notation "stable" => subtract F P π₁
local notation "wx" => WilsonMeasuredRankedPrimaryBudget.wrap F Y

theorem original {κ b:ℝ} (shape:P.Format o Y W) (fee:P.remBound o W κ b)
    (rank:d ≤ W.p.order) (power:d ≤ W.p.power) (support:W.p.supportExponent ≤ 100) :
    (stable).Format o Y W ∧ (stable).remBound o W κ b ∧
    projection F Y W.p.threshold o stable=0 ∧
    (∀ U,P.density o S W U=(stable).density o S W U+(W.eval U:ℂ)*sectionValue F S o W π₁ U) ∧
    F.coeffSize (stable).x≤wx*b ∧ F.coeffSize π₁≤F.coeffSize P.x+wx*b := by
  have old:(germ_close F Y).choose*wraps W.p n*b≥‖π₁-P.x‖:=
    (germ_close F Y).choose_spec.2 W P shape fee rank power
  have count : F.coeffSize (P.x-π₁) ≤ WilsonMeasuredRankedGerm.wrapCost F Y * wraps W.p n*b := by
    unfold Frame.coeffSize
    calc
      _ ≤ ∑ _i:F.Index,(germ_close F Y).choose*wraps W.p n*b:=Finset.sum_le_sum (fun i _=>
        (norm_le_pi_norm (P.x-π₁) i).trans ((norm_sub_rev ..).trans_le old))
      _ = _:=by simp [WilsonMeasuredRankedGerm.wrapCost];ring
  have bn : 0 ≤ b:=by obtain ⟨r,h,pr,ph,pay,_⟩:=fee;linarith only [pr,ph,pay]
  have priced:F.coeffSize (P.x-π₁)≤wx*b:=
    count.trans (mul_le_mul_of_nonneg_right (WilsonMeasuredRankedPrimaryBudget.bounded_wrap F Y W.p n support) bn)
  have head:F.coeffSize π₁≤F.coeffSize P.x+F.coeffSize (P.x-π₁):=by
    unfold Frame.coeffSize
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _=>by
      rw [Pi.sub_apply,norm_sub_rev]
      exact norm_le_norm_add_norm_sub' ..)
  refine ⟨⟨shape.smooth,shape.origin,shape.identity_null,shape.projects,shape.forcing,shape.carried,
    shape.invariant,shape.supported,shape.borel⟩,fee,?_,all_fields F S o W P π₁,priced,head.trans (add_le_add le_rfl priced)⟩
  change P.x-(P.x+∑' i,vector F Y W.p.threshold o (P.regular i)) +
    (∑' i,vector F Y W.p.threshold o (P.regular i))=0
  abel

theorem counted {κ b:ℝ} (shape:P.Format o Y W) (fee:P.remBound o W κ b)
    (rank:d ≤ W.p.order) (power:d ≤ W.p.power) :
    Summable (fun i=>vector F Y W.p.threshold o (P.regular i)) ∧
      π₁=P.x+∑' i,vector F Y W.p.threshold o (P.regular i) :=
  ⟨vector_summable F Y shape fee rank power,rfl⟩
end YM.Integration.WilsonMeasuredSectionCorrection
