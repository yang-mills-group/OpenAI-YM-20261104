import YM.MSbar.DeltaM.Town
import YM.MSbar.Pulse.Spot
import YM.MSbar.Lease.Bench
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Counting
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bakery.Film
open Function Filter MeasureTheory Cacao Whisk Kelvin RG Lattice Wilson Tree
open scoped Topology BigOperators Classical ContDiff
open Matrix Further.GaussianScalar Analysis Bakery Lattice Precision Push.Uniform
open Next.SectorChange Heath Bulk Heath.Stock Heath.Cottage
variable {G : Gauge} {c f:Side}{S:StepData c f}{p a :ℕ}
    {T W A B t s u α β Z:ℝ}
set_option quotPrecheck false
variable (J:Voice G) (F : Forest S.ratio)
variable (X Y: Support f) (V: Config G c) (U : Config G f)
local notation "I"=> board F X
local notation "A!"=>↥(board F X)
local notation "ρ!"=> fence F (board F X) G -- ambiguous
local notation "Z!"=> Config G f
local notation "W!"=>IV F (board F X) G
abbrev SpaceP (F:Forest S.ratio) (X:Support f)(G:Gauge):= Prices G (↥(board F X))
local notation "X!"=> SpaceP F X G
variable (m: SpaceP F X G)
-- Log reference **absolute log**, Input matrixGaussian reweight with no changed test.Move U chart included. m native. 
def orbitJ (Z : Z!) : W! := fun k=> (canoe (S:=S) F Z k.val.val)⁻¹
def PBody (U:Z!) : LogArray G ↥(board F X) → W!:= release (orbitJ F X U)
def draw (U: Config G f) (m:SpaceP F X G)(g:ℝ)(w:X!): Z!:=
    twirl F (board F X) (PBody F X U (tape (m+g •w))) U
local notation "K!"=>draw F X U m t
variable (ν : Positions (Key F G))(γ:ChartRatio G)
local notation "Y!"=> hotel F X Y J V ν A B
def clipM (Y:Support f) (A:Set (Config G f))(γ: ChartRatio G)(t:ℝ) (m:SpaceP F X G)(U : Z!):Set (SpaceP F X G) := {w| draw F X U m t w∈ A ∧ tape (G:=G) (m+t •w: Prices G ↥(board F X)) ∈ mouth γ}
def fLog (γ:ChartRatio G)(t:ℝ)(z: X!)(m:SpaceP F X G)(U:Z!)(L:Z!→ℝ)(B:Matrix (↥(board F X) × G.ColorIndex) (↥(board F X) × G.ColorIndex) ℝ):= L (draw F X U m t z)+ Real.log (Next.SectorChange.pay γ (tape (m+t •z: Prices G ↥(board F X))))+dotProduct z (B⁻¹ *ᵥ z) /2
variable (R:Rep G f)(i:S.Choices)
local notation "L"=> rental F J R Y i V ν
local notation "z!"=> clipM F X Y Y! γ t m U
variable (g:LocalRatio γ) (C:Matrix (↥(board F X)× G.ColorIndex) (↥(board F X)× G.ColorIndex) ℝ) 
local notation "φ!"=> fLog F X γ t
local notation "Γ"=> Portal.purse z! (fun w:X!=> fLog F X γ t w m U (rental F J R Y i V ν) C)
local notation "ρ"=>fieldLaw C
local notation "q!"=> twirl F (board F X)
lemma tape_it (t:ℝ) (v:X!)(i:A!) : canoe (S:=S) F (draw F X U m t v) i.val.val= G.lieExp ((tape (G:=G) (m+t•v : Prices G ↥(board F X))) i):=by unfold draw twirl; rw [stationary, pegged]; rw [dif_pos i.prop]; dsimp only [PBody,release,orbitJ]; group
include g
variable (e: Config G f → ℝ)
-- The hypotheses include a seal for Y and a map into the covered contour.
variable (hX:Seal S (youth F Y) (hotel F X Y J V ν A B))
variable (hm:Set.MapsTo (fun t:IV F (board F X) G=> t) {v| twirl F (board F X) v U∈hotel F X Y J V ν A B} (covered γ (orbitJ F X U)))
variable (hA: GaugeLocal S (youth F Y) (rental F J R Y i V ν)) (hc:C.PosDef)
variable (ht:0<t)
include hm ht hA hX hc
local notation "E!"=> t^(Fintype.card ((I) × G.ColorIndex))* modeCost C
end YM.MSbar.Bakery.Film
