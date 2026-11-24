import YM.Integration.WilsonGeneralReducedPhysicalSelfFullWord

/-! The entire normalized reflected Wilson word is sampled at all actual sites
of the smooth packet on one finite board. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonGeneralReducedPhysicalSelfMeasure
open Filter Set Function Finset MeasureTheory Lattice Maxwell MS MS.Land MS.Menus Local.Physical
open XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register Table.Pairing PowerSeries
open WilsonPositionProgramPublicBulb WilsonPositionProgramPublicReflectedRead WilsonPositionProgramPublicDirectoryCoin
open WilsonPositionProgramPublicContrast (assay)
open WilsonOriginalPublicPlantedGram (measured)
open WilsonGeneralReducedPhysicalSelfFullWord (finiteWord)
open WilsonIndependentFittedReflectedGram (fields stamped)
open WilsonIndependentFittedNumericalProduct (pivot)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonPositionProgramPublicDirectoryBoard (table)
open private sampled measurable_read from YM.Integration.WilsonPositionProgramPublicDirectoryBoard
open scoped Classical BigOperators Topology
variable {G:Gauge}(Z:WilsonPrescription G)(a:Axis){B:Deck G}{h:ℕ}
local notation "I" => Glyph B h
local notation "leg" => (id : I→I)

private def placed (M:Mesh)(c:Four ℝ)(z:Fin 2→M.Sites):Sample 2:=⟨M,fun i=>lift (z i),c⟩

private theorem wrapped (j:ℕ){cap:ℕ}(P:Handoff.Directory Z j cap)(s:Sample 2)(i k:I)(q:ℕ)(u:ℝ)
    (board:s.F=Z.run.step j)(room:Handoff.Directory.budget G 2 h+q≤cap):
    measured Z a leg q P u s i k=measured Z a leg q P u (placed s.F s.center (chartV s)) i k:=by
  let seen:=placed s.F s.center (chartV s)
  have one : ∀i,chartV seen i=chartV s i:=fun i=>Lattice.wrap_lift (chartV s i)
  have letters : fields Z a leg j seen=fields Z a leg j s:=by
    funext i x
    fin_cases i <;>simp only [fields,
      WilsonOriginalPublicPlantedGramFilms.reflected,WilsonOriginalPublicPlantedGramFilms.pupil,
      WilsonOriginalPublicPlantedPivotFields.plant,one,Rose.regal] <;>rfl
  rw [←stamped Z a leg j P s i k q u board room,←stamped Z a leg j P seen i k q u board room]
  exact congrArg (cash q u) (congrArg (fun P=>pivot Z.scheme s P ![i,k]) letters.symm)

private theorem entry (b:Bulb (center a) a)(j:ℕ){cap:ℕ}(P:Handoff.Directory Z j cap)
    (q:ℕ)(u:ℝ)(c:Four ℝ)(i k:I)(room:Handoff.Directory.budget G 2 h+q≤cap):
    Integrable fun y:Pair=>weight a b y • measured Z a leg q P u (node a (Z.run.step j) c y) i k:=by
  let M:=Z.run.step j
  let fee (z:Fin 2→M.Sites):ℝ:=‖measured Z a leg q P u (placed M c z) i k‖
  have limited(y:Pair):‖measured Z a leg q P u (node a M c y) i k‖≤∑z,fee z:=by
    calc
      _=fee (chartV (node a M c y)):=congrArg norm (wrapped Z a j P (node a M c y) i k q u rfl room)
      _≤_:=Finset.single_le_sum (f:=fee) (fun x _=>norm_nonneg _) (mem_univ (chartV (node a M c y)))
  exact sampled a b _ (measurable_read a (drawValue Z (signed a leg i k) q P u) M c)
    (t:=∑z,fee z) (fun y _=>limited y)

def whole (b:Bulb (center a) a)(j q:ℕ)(u:ℝ)(c:Four ℝ)(d:I→ℂ):ℂ:=
  ∫y:Pair,weight a b y • cash q u (finiteWord Z a j (node a (Z.run.step j) c y) d)

theorem original (b:Bulb (center a) a)(j:ℕ){cap:ℕ}(P:Handoff.Directory Z j cap)
    (q:ℕ)(u:ℝ)(c:Four ℝ)(d:I→ℂ)(room:Handoff.Directory.budget G 2 h+q≤cap):
    whole Z a b j q u c d=assay d d (table Z a b q leg P u c):=by
  let read (i k:I)(y:Pair):ℂ:=weight a b y • measured Z a leg q P u (node a (Z.run.step j) c y) i k
  let dose (i k:I):ℂ:=star (d i)*d k
  have inc(i k:I):Integrable (fun y=>dose i k*read i k y):=(entry Z a b j P q u c i k room).const_mul _
  calc
    _=∫y:Pair,∑i:I,∑k:I,dose i k*read i k y:=by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      change weight a b y • cash q u (finiteWord Z a j (node a (Z.run.step j) c y) d)=_
      rw [WilsonGeneralReducedPhysicalSelfFullWord.atNode Z a j P (node a (Z.run.step j) c y) d q u rfl room]
      simp only [assay,Finset.smul_sum,read,dose,Algebra.mul_smul_comm]
    _=∑i:I,∑k:I,∫y:Pair,dose i k*read i k y:=by
      rw [integral_finsetSum _ (fun i _=>integrable_finsetSum _ fun k _=>inc i k)]
      apply sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun k _=>inc i k)
    _=_:=by
      simp only [integral_const_mul,assay,dose]
      rfl

end YM.Integration.WilsonGeneralReducedPhysicalSelfMeasure
