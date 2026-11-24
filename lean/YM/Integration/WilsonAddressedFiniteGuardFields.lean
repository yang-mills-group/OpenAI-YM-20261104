import YM.Integration.WilsonOriginalMicroscopicGuardedWallet
import YM.Integration.WilsonOriginalAlternativeTrialSource
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedFiniteGuardFields
open Filter Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Extra.Multi
open PhysicalNext.Repeat.Legato Push.AbsoluteSums.Animals
open WilsonPositionProgramOriginalBlockedTrial WilsonPositionProgramBlockedTrialAddBack
open scoped Classical BigOperators

variable {I:Type} {G:Gauge} (R:Run G) (d:I  →  ℕ) (N p K:ℕ)
local notation "F" a:max => R.family.labels.level (d a)
local notation "S" a:max => R.family.localSection (d a)
local notation "W" => R.family.path.rep N p K
local notation "X" => Config G (R.family.side K p)
variable (o:I  →  Site (R.family.side K p)) (v:∀a:I,R.family.label (d a))

def guarded (a:I)(U:X):ℂ:=part (S a) (o a) (W) U (v a)
def raw (a:I):X → ℂ:=uncut R (d a) N p K (o a) (v a)
def cap (a:I):ℝ:=
  ‖v a 0‖+BasisCost.price (S a)*(F a).coeffSize (names R (d a) N p K (v a))

def face {Space:Type*} (A:I → Space → ℂ)(s:Finset (I))(U:Space):ℂ:=∏a∈s,A a U

def footprint (s:Finset (I)):Support (R.family.side K p):=s.biUnion fun a=>(S a).footprint (o a)

local notation "old" => guarded R d N p K o v
local notation "new₀" => raw R d N p K o v
local notation "span₀" s:max => footprint R d p K o s
local notation "head₀" a:max => names R (d a) N p K (v a)
local notation "bound₀" => cap R d N p K v

theorem source (live:K  ≤  N)(a:I)(U:X):
    ((W).eval U:ℂ)*(old) a U=numerator R (d a) N p K (o a) (v a) U ∧
    (new₀) a U=∑l,WilsonPositionProgramReportedField.entire R (d a) K (N,p) (v a) l*
      WilsonPositionProgramBlockedTrialFiling.atomAt R (d a) N p K (o a) l U:=
  WilsonOriginalMicroscopicGuardedTrial.source R (fun _:Fin 3=>d a) N p K (fun _=>o a) (fun _=>v a) live 0 U

theorem unary (a:I):Measurable ((old) a) ∧ Measurable ((new₀) a) ∧
    ∀U:X,‖(old) a U‖  ≤  (bound₀) a ∧ ‖(new₀) a U‖  ≤  (bound₀) a:=
  WilsonOriginalMicroscopicGuardedTrial.unary R (fun _:Fin 3=>d a) N p K (fun _=>o a) (fun _=>v a) 0

def gap (s:Finset (I))(U:X):ℂ:=face (new₀) s U-face (old) s U
local notation "delta₀" s:max => gap R d N p K o v s

theorem occupied (s:Finset (I)):
    let E:=SelectedCofactorAnchoredRegister.hot (G:=G) (W).p.threshold (span₀ s)
    Measurable (delta₀ s) ∧ (∀U:X,‖(delta₀ s) U‖  ≤  2*∏a∈s,(bound₀) a) ∧
    (∀U:X,U∉E → (delta₀ s) U=0) ∧
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
    have h (A:I → X → ℂ)(fund:∀a,‖A a U‖  ≤  (bound₀) a):
        ‖face A s U‖  ≤  ∏a∈s,(bound₀) a:=by
      rw [face,norm_prod];exact prod_le_prod (fun _ _=>norm_nonneg _) (fun a _=>fund a)
    exact (norm_sub_le ..).trans ((add_le_add (h _ fun a=>((held a).2.2 U).2)
      (h _ fun a=>((held a).2.2 U).1)).trans_eq (two_mul _).symm)
  · funext U
    by_cases atSite:U∈E
    · exact (Set.indicator_of_mem atSite _).trans (one_smul ℝ _)
    · exact (Set.indicator_of_notMem atSite _).trans (away U atSite).symm


theorem tuned (z:I → ℂ)(a:I)(U:X):
    guarded R d N p K o (fun j=>z j • v j) a U=WilsonOriginalAlternativeTrialSource.arm R d N p K o v z a U:=by
  unfold guarded WilsonOriginalAlternativeTrialSource.arm
  rw [LinearMap.map_smul,smul_eq_mul]

theorem budget (live:K ≤ N)(a:I):cap R d N p K v a ≤ WilsonOriginalMicroscopicGuardedWallet.loss R (d a) K*((F a).coeffSize (v a)):=
  WilsonOriginalMicroscopicGuardedWallet.one R (fun _:Fin 3=>d a) N p K live (fun _=>v a) 0

end YM.Integration.WilsonAddressedFiniteGuardFields
end
