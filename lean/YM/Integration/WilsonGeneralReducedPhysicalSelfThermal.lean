import YM.Integration.WilsonGeneralReducedPhysicalSelfMeasure

/-! Evaluating the complete formal reannouncement of the original deposited
vector expends its raw word salary only above the retained thermal order. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonGeneralReducedPhysicalSelfThermal
open Filter Function Finset Set MeasureTheory Lattice MS MS.Land MS.Menus Local.Physical
open XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register Table.Pairing PowerSeries
open WilsonPositionProgramPublicBulb WilsonPositionProgramPublicReflectedRead
open WilsonPositionProgramPublicContrast (assay)
open WilsonOriginalPublicPlantedGram (measured)
open WilsonIndependentFittedReflectedGram (fields paired)
open WilsonIndependentFittedNumericalProduct (fitted gross)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonGeneralReducedPhysicalSelfFullWord (finiteWord atNode)
open WilsonGeneralReducedPhysicalSelfMeasure (whole)
open private placed wrapped from YM.Integration.WilsonGeneralReducedPhysicalSelfMeasure
open private difference measurable_read from YM.Integration.WilsonPositionProgramPublicDirectoryBoard
open scoped Classical BigOperators Topology
variable {G:Gauge}(Z:WilsonPrescription G)(a:Axis){B:Deck G}{h:ℕ}
local notation "I" => Glyph B h
local notation "leg" => (id : I→I)

def suspended (j:ℕ)(s:Sample 2)(D:I→PowerSeries ℂ):PowerSeries ℂ:=
  fitted Z.scheme s (fields Z a leg j s) (paired D)

def salary (j q:ℕ)(s:Sample 2)(D:I→PowerSeries ℂ):ℝ:=
  gross Z.scheme s (fields Z a leg j s) (paired D) q

def retained (b:Bulb (center a) a)(j q:ℕ)(u:ℝ)(c:Four ℝ)(D:I→PowerSeries ℂ):ℂ:=
  ∫y:Pair,weight a b y • cash q u (suspended Z a j (node a (Z.run.step j) c y) D)

theorem one (j q:ℕ){cap:ℕ}(P:Handoff.Directory Z j cap)(s:Sample 2)(D:I→PowerSeries ℂ)(u:ℝ)
    (board:s.F=Z.run.step j)(room:Handoff.Directory.budget G 2 h+q≤cap)(cold:|u|≤1):
    ‖cash q u (suspended Z a j s D)-cash q u (finiteWord Z a j s (fun i=>cash q u (D i)))‖≤
      3*|u|^(q+1)*salary Z a j q s D:=by
  rw [atNode Z a j P s _ q u board room,←WilsonIndependentFittedReflectedGram.purchased Z a leg j P s D q q u board room]
  simpa only [suspended,salary,Fintype.card_fin,Nat.cast_ofNat,show (2:ℝ)+1=3 by norm_num] using
    WilsonIndependentFittedNumericalProduct.regroup Z.scheme s (fields Z a leg j s) (paired D) q cold

private theorem oneSite (j q:ℕ){cap:ℕ}(P:Handoff.Directory Z j cap)(s:Sample 2)(d:I→ℂ)(u:ℝ)
    (board:s.F=Z.run.step j)(room:Handoff.Directory.budget G 2 h+q≤cap):
    cash q u (finiteWord Z a j s d)=cash q u (finiteWord Z a j (placed s.F s.center (chartV s)) d):=by
  let same:=placed s.F s.center (chartV s)
  calc
    _=assay d d (measured Z a leg q P u s):=atNode Z a j P s d q u board room
    _=assay d d (measured Z a leg q P u same):=congrArg (assay d d)
      (funext fun i=>funext fun k=>wrapped Z a j P s i k q u board room)
    _=_:=(atNode Z a j P same d q u board room).symm

theorem original (b:Bulb (center a) a)(j q:ℕ){cap:ℕ}(P:Handoff.Directory Z j cap)
    (u:ℝ)(c:Four ℝ)(D:I→PowerSeries ℂ)(room:Handoff.Directory.budget G 2 h+q≤cap)(cold:|u|≤1)
    (fee:ℝ)(paid:∀y:Pair,weight a b y≠0→salary Z a j q (node a (Z.run.step j) c y) D≤fee):
    ‖retained Z a b j q u c D-whole Z a b j q u c (fun i=>cash q u (D i))‖≤3*|u|^(q+1)*fee:=by
  let M:=Z.run.step j
  let d:=fun i=>cash q u (D i)
  let value (s:Sample 2):ℂ:=cash q u (finiteWord Z a j s d)
  let mass (z:Fin 2→M.Sites):ℝ:=‖value (placed M c z)‖
  have charge(y:Pair):‖value (node a M c y)‖≤∑z,mass z:=by
    calc
      _=mass (chartV (node a M c y)):=congrArg norm (oneSite Z a j q P (node a M c y) d u rfl room)
      _≤_:=single_le_sum (f:=mass) (fun z _=>norm_nonneg _) (mem_univ (chartV (node a M c y)))
  apply difference a b _ _
    (measurable_read a (fun p=>cash q u (suspended Z a j ⟨M,p,c⟩ D)) M c)
    (measurable_read a (fun p=>value ⟨M,p,c⟩) M c) (fun y _=>charge y)
  intro y hy
  exact (one Z a j q P (node a M c y) D u rfl room cold).trans
    (mul_le_mul_of_nonneg_left (paid y hy) (by positivity))

end YM.Integration.WilsonGeneralReducedPhysicalSelfThermal
