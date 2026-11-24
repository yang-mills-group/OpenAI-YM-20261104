import YM.Integration.WilsonSurveyedEquationFrameBasis
import YM.Integration.WilsonIndependentMatchedFiledIncome

/-! The common fit is an actual Wilson section, equivariant and real. Its full
thermal row can be submitted, including every field and address on this chart. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonSurveyedEquationFrameFiled
open Lattice RG Wilson Labels Source Maxwell Maxwell.Free Push Push.Mark XSpace
open WilsonSurveyedEquationFrameBasis (projection kernel read mixed)
open scoped BigOperators Classical
variable {G : Gauge} {d : ℕ}

theorem projectedTurn (s : Signed) (p : Label G d) :
    projection (theta s p) = theta s (projection p) :=
  On.section_turn s ((observable G d).rangeRestrict p)
    ((observable G d).rangeRestrict (theta s p)) (pulls_label p s.ortho).symm

theorem projectedConj (p : Label G d) : projection (realBar p) = realBar (projection p) :=
  On.section_real ((observable G d).rangeRestrict p) ((observable G d).rangeRestrict (realBar p))
    (real_eats p).symm

theorem kernelTurn (s : Signed) (p : Label G d) :
    kernel (theta s p) = theta s (kernel p) := by
  simp only [kernel,LinearMap.sub_apply,LinearMap.id_apply,projectedTurn,map_sub]

theorem kernelConj (p : Label G d) : kernel (realBar p) = realBar (kernel p) := by
  simp only [kernel,LinearMap.sub_apply,LinearMap.id_apply,projectedConj,map_sub]

variable (F : Labels.Frame G d) (H : Hol G) (S : SectionData F)

private theorem storedTurn (ok : S.Sound H) (s : Signed) (p : Label G d) :
    read F S (theta s p) = read F S p ∘ pull s 0 := by
  funext U
  change S.evaluate (F.coords (tensor s.ortho p)) U=S.evaluate (F.coords p) (pull s 0 U)
  rw [ok.Hpart,Frame.act_coords]

private theorem storedConj (ok : S.Sound H) (p : Label G d) :
    read F S (realBar p) = star (read F S p) := by
  have hh : F.coords (realBar p)=star (F.coords p) := by
    funext i
    have eq := F.conj_basis (F.coords p) i
    rw [LinearEquiv.symm_apply_apply] at eq
    exact eq
  funext U
  change S.evaluate (F.coords (realBar p)) U=star (S.evaluate (F.coords p) U)
  rw [hh,ok.ordinary_real]

private theorem display (J : Switch G d) (p : Label G d) :
    mixed F S J p = (projection p,read F S (projection p)) + J (kernel p) := rfl

theorem imprinted (ok : S.Sound H) (wage : Bid.pop S) {J : Switch G d} (issued : Imprint H d J) :
    Imprint H d (mixed F S J) := by
  refine ⟨WilsonSurveyedEquationFrameBasis.complete F H S J issued.toCampaign ok wage,?_,?_⟩
  · intro s p
    rw [display,display,projectedTurn,kernelTurn,issued.signed,map_add,storedTurn F H S ok]
    rfl
  · intro p
    rw [display,display,projectedConj,kernelConj,issued.real_,map_add,storedConj F H S ok]
    rfl

/-- One filed stencil for every raw input. On all link configurations its
value is the surveyed physical word plus the original exact equation word.
The same stencil has the declared thermal and rooted admission. -/
theorem original (W : Initialize G) :
    ∃ (S V U : SectionData F) (A P : Label G d ≃ₗ[ℂ] Label G d),
    (W.surveys d).Represents F S ∧ Portfolio W.hol V A ∧ Portfolio W.hol U P ∧
    (∀ p, P p = projection p + A (kernel p)) ∧
    (∀ p, U.evaluate (F.coords (P p)) =
      S.evaluate (F.coords (projection p)) + V.evaluate (F.coords (A (kernel p)))) := by
  obtain ⟨S,ok⟩ := (W.surveys d).prepares F
  obtain ⟨J₀,h₀⟩ := unsym W.hol d
  let ht := impression h₀
  let joined := imprinted F W.hol S ok.1 ok.2.1 ht
  obtain ⟨V,old,paid⟩ := weaveBuild ht F
  obtain ⟨U,new,print⟩ := weaveBuild joined F
  refine ⟨S,V,U,_,_,ok,old,new,fun _ => rfl,?_⟩
  intro p
  rw [print,paid]
  rfl

end YM.Integration.WilsonSurveyedEquationFrameFiled
