import YM.Integration.WilsonOriginalObservedRoseFiniteReturn
import YM.Integration.WilsonOriginalObservedRoseSevenScale
import YM.Integration.WilsonOlderFreshSoftSocketStationPortfolio

/-! Compare the dimensionally restored stopped table with the finite, unsubtracted Galop on each cell. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornLedger
open Finset PowerSeries RG Lattice Wilson PhysicalNext.Repeat.Legato
open Maxwell XSpace XSpace.Normalize XSpace.Rose XSpace.Structure1 XSpace.Cirrus XSpace.Photo
open WilsonPositionThermometerConnected (value)
open WilsonOriginalObservedRoseSevenScale (plant)
open WilsonOlderFreshSoftSocketStationPortfolio (reading)
open WilsonOriginalObservedRoseFiniteReturn (target edge charge)
open WilsonOriginalObservedRoseTruncatedFaces (fee)
open private graded from YM.Integration.WilsonOriginalObservedRoseSevenScale
open scoped Classical BigOperators
variable {G:Gauge}(D:Initialize G){V:Store G}{Y:Type}[Fintype Y]
    (μ:Y→ℂ)(r:ℝ)(points:Y→Sample 3)(tags:Tags G 6 3)(j:ℕ)(g:ℂ)(rows:Y→Badge→ℂ)

def center:ℂ:=∑y,μ y*target D (V:=V) (points y) tags j g

def debit:ℂ:=∑y,μ y*edge D (V:=V) (points y) tags j g (plant r (rows y))

def cost:ℝ:=∑y,‖μ y‖*charge D (V:=V) (points y) tags j g (plant r (rows y))

def truncation:ℝ:=(∑y,‖μ y‖*fee (WilsonOriginalObservedRoseProgram.face D (V:=V) (points y) tags) j)*‖g‖^(j+1)

local notation "C₀"=>center D (V:=V) μ points tags j g
local notation "E₀"=>debit D (V:=V) μ r points tags j g rows
local notation "B₀"=>cost D (V:=V) μ r points tags j g rows
local notation "T₀"=>truncation D (V:=V) μ points tags j g
local notation "P₀"=>reading μ ((r:ℂ)^14) rows

theorem original (hg:‖g‖≤1):
    ‖P₀-C₀-E₀‖≤T₀ ∧ ‖P₀-C₀‖≤T₀+B₀:=by
  classical
  let p:=fun y=>plant r (rows y)
  let a:=fun y=>target D (V:=V) (points y) tags j g
  let e:=fun y=>edge D (V:=V) (points y) tags j g (p y)
  have signed (y:Y):‖value (p y)-a y-e y‖≤fee (WilsonOriginalObservedRoseProgram.face D
      (V:=V) (points y) tags) j*‖g‖^(j+1):=by
    simpa using WilsonOriginalObservedRoseFiniteReturn.cleared D (V:=V) (points y) tags j g (p y)
      (value (p y)) 0 0 hg (by simp)
  have budget (y:Y):‖e y‖≤charge D (V:=V) (points y) tags j g (p y):=by
    dsimp only [e,edge,charge]
    exact (norm_sum_le ..).trans (by simp only [norm_mul,le_refl])
  have split:P₀-C₀-E₀=∑y,μ y*(value (p y)-a y-e y):=by
    simp only [reading,center,debit,p,a,e,graded,mul_sub,Finset.sum_sub_distrib]
  have cut:‖P₀-C₀-E₀‖≤T₀:=by
    rw [split]
    refine (norm_sum_le ..).trans ?_
    rw [truncation,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro y _
    rw [norm_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (signed y) (norm_nonneg _)
  refine ⟨cut,?_⟩
  have wages:‖E₀‖≤B₀:=by
    unfold debit cost
    refine (norm_sum_le ..).trans (Finset.sum_le_sum (fun y _=>?_))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (budget y) (norm_nonneg _)
  calc
    ‖P₀-C₀‖=‖(P₀-C₀-E₀)+E₀‖:=by rw [sub_add_cancel]
    _≤_ := (norm_add_le ..).trans (add_le_add cut wages)

theorem observed (hg:‖g‖≤1)(raw:ℂ)(earned:ℝ)(sale:‖raw-P₀‖≤earned):
    ‖raw-C₀-E₀‖≤earned+T₀ ∧ ‖raw-C₀‖≤earned+T₀+B₀:=by
  obtain ⟨first,total⟩:=original D μ r points tags j g rows hg
  constructor
  · calc
      ‖raw-C₀-E₀‖=‖(raw-P₀)+(P₀-C₀-E₀)‖:=by congr 1;ring
      _≤_ := (norm_add_le ..).trans (add_le_add sale first)
  · calc
      ‖raw-C₀‖=‖(raw-P₀)+(P₀-C₀)‖:=by congr 1;ring
      _≤earned+(T₀+B₀):= (norm_add_le ..).trans (add_le_add sale total)
      _=_:=by ring

end YM.Integration.WilsonOriginalObservedRoseBornLedger
