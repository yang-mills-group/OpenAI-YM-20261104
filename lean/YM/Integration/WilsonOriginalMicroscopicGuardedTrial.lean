import YM.Integration.WilsonPositionProgramBlockedTrialAddBack
import YM.Integration.WilsonPositionProgramBlockedTrialFiling

/-! Joint ordinary faces of the canonical deposited trial on one actual
Wilson configuration. Its scalar is present on a failed stencil. Removing
the guards changes a face only on that face's own union of hot sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicGuardedTrial
open Filter Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Extra.Multi
open PhysicalNext.Repeat.Legato Push.AbsoluteSums.Animals
open WilsonPositionProgramOriginalBlockedTrial WilsonPositionProgramBlockedTrialAddBack
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (d:Fin 3 → ℕ) (N p K:ℕ)
local notation "F" a:max => R.family.labels.level (d a)
local notation "S" a:max => R.family.localSection (d a)
local notation "W" => R.family.path.rep N p K
local notation "X" => Config G (R.family.side K p)
variable (o:Fin 3 → Site (R.family.side K p)) (v:∀a:Fin 3,R.family.label (d a))

def guarded (a:Fin 3)(U:X):ℂ:=part (S a) (o a) (W) U (v a)
def raw (a:Fin 3):X→ℂ:=uncut R (d a) N p K (o a) (v a)
def cap (a:Fin 3):ℝ:=
  ‖v a 0‖+BasisCost.price (S a)*(F a).coeffSize (names R (d a) N p K (v a))

def face {Space:Type*} (A:Fin 3→Space→ℂ)(s:Finset (Fin 3))(U:Space):ℂ:=∏a∈s,A a U

def footprint (s:Finset (Fin 3)):Support (R.family.side K p):=s.biUnion fun a=>(S a).footprint (o a)

local notation "old" => guarded R d N p K o v
local notation "new₀" => raw R d N p K o v
local notation "span₀" s:max => footprint R d p K o s
local notation "head₀" a:max => names R (d a) N p K (v a)
local notation "bound₀" => cap R d N p K v

theorem source (live:K ≤ N)(a:Fin 3)(U:X):
    ((W).eval U:ℂ)*(old) a U=numerator R (d a) N p K (o a) (v a) U ∧
    (new₀) a U=∑l,WilsonPositionProgramReportedField.entire R (d a) K (N,p) (v a) l*
      WilsonPositionProgramBlockedTrialFiling.atomAt R (d a) N p K (o a) l U:=
  ⟨(original_field R (d a) N p K (o a) (v a) U).symm,
    WilsonPositionProgramBlockedTrialFiling.filed R (d a) N p K live (o a) (v a) U⟩

theorem unary (a:Fin 3):Measurable ((old) a) ∧ Measurable ((new₀) a) ∧
    ∀U:X,‖(old) a U‖ ≤ (bound₀) a ∧ ‖(new₀) a U‖ ≤ (bound₀) a:=by
  let f: X→ℂ:=(S a).places (head₀ a) (o a)
  let E:=(S a).footprint (o a)
  have smooth:Measurable f:=((S a).continuous_places _ _).measurable
  refine ⟨measurable_const.add (RG.masked_measurable (W).p.threshold E f smooth),
    measurable_const.add smooth,?_⟩
  intro U
  have h:‖f U‖ ≤ BasisCost.price (S a)*(F a).coeffSize (head₀ a):=BasisCost.full (S a) _ (o a) U
  have m:‖masked (W).p.threshold E f U‖ ≤ ‖f U‖:=by
    by_cases healthy:Healthy (W).p.threshold E U
    · rw [masked_eq _ _ _ _ healthy]
    · rw [masked_ne _ _ _ _ healthy,norm_zero];exact norm_nonneg _
  exact ⟨(norm_add_le _ _).trans (add_le_add le_rfl (m.trans h)),
    (norm_add_le _ _).trans (add_le_add le_rfl h)⟩

def gap (s:Finset (Fin 3))(U:X):ℂ:=face (new₀) s U-face (old) s U
local notation "delta₀" s:max => gap R d N p K o v s

theorem occupied (s:Finset (Fin 3)):
    let E:=SelectedCofactorAnchoredRegister.hot (G:=G) (W).p.threshold (span₀ s)
    Measurable (delta₀ s) ∧ (∀U:X,‖(delta₀ s) U‖ ≤ 2*∏a∈s,(bound₀) a) ∧
    (∀U:X,U∉E→(delta₀ s) U=0) ∧
    PhysicalWilsonHotIntegral.restricted (E:=E) 1 (delta₀ s)=(delta₀ s):=by
  intro E
  have held:=unary R d N p K o v
  have yes:Measurable (face (old) s):=Finset.measurable_prod _ fun a _=>(held a).1
  have yes':Measurable (face (new₀) s):=Finset.measurable_prod _ fun a _=>(held a).2.1
  have away (U:X)(good:U∉E):(delta₀ s) U=0:=by
    apply sub_eq_zero.mpr
    apply Finset.prod_congr rfl
    intro a ha
    have ok:Healthy (W).p.threshold ((S a).footprint (o a)) U:=by
      apply Finset.disjoint_left.mpr
      intro x hx bad
      exact good ⟨x,Finset.mem_biUnion.mpr ⟨a,ha,hx⟩,bad⟩
    change _=v a 0+masked (W).p.threshold ((S a).footprint (o a)) ((S a).places (head₀ a) (o a)) U
    rw [masked_eq _ _ _ _ ok];rfl
  refine ⟨yes'.sub yes,?_,away,?_⟩
  · intro U
    have h (A:Fin 3→X→ℂ)(fund:∀a,‖A a U‖ ≤ (bound₀) a):
        ‖face A s U‖ ≤ ∏a∈s,(bound₀) a:=by
      rw [face,norm_prod];exact prod_le_prod (fun _ _=>norm_nonneg _) (fun a _=>fund a)
    exact (norm_sub_le ..).trans ((add_le_add (h _ fun a=>((held a).2.2 U).2)
      (h _ fun a=>((held a).2.2 U).1)).trans_eq (two_mul _).symm)
  · funext U
    by_cases atSite:U∈E
    · exact (Set.indicator_of_mem atSite _).trans (one_smul ℝ _)
    · exact (Set.indicator_of_notMem atSite _).trans (away U atSite).symm

end YM.Integration.WilsonOriginalMicroscopicGuardedTrial
end
