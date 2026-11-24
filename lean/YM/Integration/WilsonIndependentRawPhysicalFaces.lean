import YM.Integration.WilsonIndependentReportedRoster
import YM.Integration.WilsonOriginalPublicPlantedLetters
import YM.Integration.WilsonOriginalPublicPivotReflected

/-! The measured physical figure on each named occupied face, with its
true positions, is the finite linear combination of the funded orbit words. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentRawPhysicalFaces
open Lattice RG Source Labels XSpace PhysicalNext.Repeat.Legato Precision
open XSpace.Cirrus RegulatorIR.Motion
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Cluster RegulatorIR.Halo
open WilsonIndependentRawRosterWord (fold film)
open WilsonIndependentRawRosterBudget (span)
open WilsonThermometerPositionTunedSlope (Columns finite price paid)
open WilsonPositionProgramTrialThermalGrades (frozen)
open WilsonOriginalPublicPivotReflected (board)
open scoped Classical BigOperators PowerSeries

variable {I:Type}
structure Lists (s:Finset I)(J:Composite I):Prop where
  product:∀(A:Type)[CommMonoid A](f:I → A),fold f J=∏i∈s,f i
  reach:∀ (x:Room)(site:I → Cover),span x site J=∑i∈s,dist x (slide 1 (site i))

theorem listing (s:Finset I)(occ:s.Nonempty):∃J:Composite I, Lists s J:=by
  classical
  induction s using Finset.induction_on with
  | empty => simp at occ
  | @insert i s fresh rest =>
    by_cases present:s.Nonempty
    · obtain ⟨J,g⟩:=rest present
      refine ⟨.pair (.atom i) J,?_⟩
      constructor
      · intro A inst f
        rw [fold,fold,g.product,Finset.prod_insert fresh]
      · intro x site
        rw [span,span,g.reach,Finset.sum_insert fresh]
    · have gone:s=∅:=Finset.not_nonempty_iff_eq_empty.mp present
      subst s
      refine ⟨.atom i,?_⟩
      constructor <;> intros <;> simp [fold,span]

def ordered [Fintype I][Nonempty I]:Composite I:=(listing (Finset.univ:Finset I) Finset.univ_nonempty).choose
theorem entered [Fintype I][Nonempty I]:Lists (Finset.univ:Finset I) (ordered (I:=I)):=
  (listing (Finset.univ:Finset I) Finset.univ_nonempty).choose_spec

def survey {n:ℕ}(X:Sample n)(ray:Fin 2 → Fin n):Sample 2:=
  ⟨X.F,X.layout ∘ ray,X.center⟩

variable {G:Gauge}(R:Run G)(W:Initialize G){n:ℕ}(d:Fin n → ℕ)
    (v:(i:Fin n) → (R.family.labels.level (d i)).Coeff)
    (X:Sample n)(ray:Fin 2 → Fin n)(S:Finset (Fin n))
local notation "dₛ" => (fun i:S=>d i)
local notation "site" => (fun i:S=>X.layout i)
def weight (a:Columns R dₛ):ℂ:=∏i:S,v i (a i)

theorem received (J:Composite S)(g:Lists Finset.univ J):
    board R W d v X S=∑a:Columns R dₛ, PowerSeries.C (weight R d v S a)*
      Bare.normalized (W.tree X.F.p) G (film R W (fun _=>false) dₛ a (survey X ray) site J):=by
  unfold WilsonOriginalPublicPivotReflected.board WilsonThermometerPositionTunedSlope.paid
  apply Finset.sum_congr rfl
  intro a _
  have cash:price R dₛ (frozen R dₛ (fun i:S=>v i)) a=PowerSeries.C (weight R d v S a):=by
    rw [price,weight,map_prod]
    rfl
  change price R dₛ (frozen R dₛ (fun i:S=>v i)) a * finite R dₛ X.F.p site (W.tree X.F.p) a = _
  rw [cash,WilsonOriginalPublicPlantedLetters.original]
  apply congrArg (fun z=>PowerSeries.C (weight R d v S a)*Bare.normalized (W.tree X.F.p) G z)
  exact (g.product _ (fun i:S=>WilsonOriginalPublicPlantedLetters.letter R X.F.p (W.tree X.F.p)
    (d i) (X.layout i) (a i))).symm

theorem original (hS:S.Nonempty):
    letI : Nonempty S:=hS.to_subtype
    board R W d v X S=∑a:Columns R dₛ,PowerSeries.C (weight R d v S a)*
      Bare.normalized (W.tree X.F.p) G (film R W (fun _=>false) dₛ a (survey X ray) site ordered):=by
  letI : Nonempty S:=hS.to_subtype
  exact received R W d v X ray S ordered entered

end YM.Integration.WilsonIndependentRawPhysicalFaces
