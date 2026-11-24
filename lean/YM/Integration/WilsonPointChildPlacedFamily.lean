import YM.Integration.WilsonPointChildWindingRoot
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildPlacedFamily
open Filter Function Finset YM FormalBulk08 Lattice RG Laurent Next.Foundations PhysicalNext.Repeat.Legato
open Reef Flat Stationary Dawn Pose Kemp Palm Shore Mesa Wine Quire Roof Lotus Sierra Gorge Dove Rial Rift Lava
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep WilsonPointChildFiledPress
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped ContDiff BigOperators Topology Classical ENNReal
open Function Filter Finset Matrix Lattice Wilson RG Laurent PowerSeries Work.F08
open FormalBulk08 Flat Reef Jets Orb Wick Stationary Series Shore Gorge Lotus Mesa Rift Lava Dawn Kemp Roof Sierra Rial
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open YM Next.Foundations PhysicalNext.Repeat.Legato Pose Palm Quire Wine Dove WilsonCoeffUV.Embroider
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Classical Topology BigOperators ContDiff
open WilsonCoeffUV.Bank.Carp WilsonPointChildPairedHistory
open WilsonPointChildCoveredRead (directions)
open Function Filter Finset Lattice RG Wilson Laurent Precision PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Ticket
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open WilsonVacuumPreResetFiniteHeatTable (table)
open WilsonMarkedIndependentNormalizedWallet (gap)
open WilsonMarkedIndependentNormalizedScale (rate)
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
open Borough
open WilsonPointChildFiledSalary (inverseCost)
open WilsonPointChildFiniteRestamp (difference)
open WilsonPointChildCoverStep (routes)
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open WilsonVacuumPreResetFiniteHeatTable (table)
open WilsonMarkedIndependentNormalizedScale (rate)
open WilsonCoeffUV.Bank.Carp
open WilsonPointChildFiniteStage (Gap)
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider WilsonCoeffUV.Shard
open WilsonCoeffUV.Wheel.Mark WilsonPointChildFiledPress WilsonPointChildWindingSchool
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer
open WilsonCoeffUV.Embroider.Canvas
open private point probe angle from YM.Integration.WilsonPointChildScalarSlot
variable {G:Gauge}{ι α:Type}{r:ℕ}{D k:ι → ℕ}

theorem through {n:Side}{V Z:Type} [NormedAddCommGroup V][NormedSpace ℝ V]
    [NormedAddCommGroup Z][NormedSpace ℝ Z] {x:ι → Cover}{J:Finset ι}{s A:ℝ}
    {P:Ten V (Site n × α) r}{F:Ten V (Cloth α) r}(L:V →L[ℝ] Z)
    (h:MarkU x J P F s A):MarkU x J (L ∘ P) (L ∘ F) s (‖L‖*A):=by
  refine ⟨⟨mul_nonneg (norm_nonneg _) h.access.1,?_⟩,⟨mul_nonneg (norm_nonneg _) h.bill.1,?_⟩,
    ⟨mul_nonneg (norm_nonneg _) h.gulf.coal,?_⟩⟩
  · intro y
    exact (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (h.access.2 y) (norm_nonneg L)).trans_eq (by ring))
  · intro y
    exact (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (h.bill.2 y) (norm_nonneg L)).trans_eq (by ring))
  · intro y small
    simp only [Function.comp_apply,←map_sub]
    exact (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (h.gulf.local_w y small) (norm_nonneg L)).trans_eq (by ring))

def roster (A:(s:ι) → Era G (Pen D {s})) (J:Finset ι):Era G (Pen D J):=if h:J.card=1 then
  (card_eq_one.mp h).choose_spec.symm ▸ A (card_eq_one.mp h).choose else 0

theorem singleton (A:(s:ι) → Era G (Pen D {s}))(t:ι):roster A {t}=A t:=by
  unfold roster
  split
  next h =>
    have hit:(card_eq_one.mp h).choose=t:=(Finset.singleton_inj.mp (card_eq_one.mp h).choose_spec).symm
    have exactAt(s:ι)(hs:s=t):∀w,Eq.rec (motive:=fun J _=>Era G (Pen D J)) (A s) w=A t:=by
      subst s
      intro
      rfl
    exact exactAt _ hit _
  next h => exact False.elim (h (card_singleton _))

theorem other (A:(s:ι) → Era G (Pen D {s})){J:Finset ι}(h:J.card≠1):roster A J=0:=dif_neg h

theorem legal (A:(s:ι) → Era G (Pen D {s}))(h:∀s,Auth (k s) (A s)):Eu k (roster A):=by
  intro J
  by_cases one:J.card=1
  · obtain ⟨s,rfl⟩:=card_eq_one.mp one
    simpa only [singleton,mass,sum_singleton] using h s
  rw [other A one]
  exact unstamped

def charge (t:ι):ℝ →L[ℝ] Pen (fun _:ι=>0) {t}:=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (petal (fun _:ι=>0) t point)

theorem captured (t:ι)(c:ℝ):touch (fun _:ι=>page 0 probe) {t} (charge t c)=c:=by
  change touch _ {t} (c • petal (fun _:ι=>0) t point)=c
  rw [map_smul,petal_hit]
  change c*(write 0 probe angle zeroC)=c
  rw [Embroider.draft]
  change c*(iteratedFDeriv ℝ 0 probe.val zeroC.val _)=c
  rw [iteratedFDeriv_zero_apply]
  exact mul_one c

/-- Each pretested filed source is inserted under its own genuine marker
with its own original deck and cover site. -/
def placed (X:ι → Era G ℝ)(L:(s:ι) → ℝ →L[ℝ] Pen D {s})(y:ι → Cover):family G D:=
  roster (fun s=>tuftV (L s) (shifted (X s) (y s)))

theorem field (X:ι → Era G ℝ)(L:(s:ι) → ℝ →L[ℝ] Pen D {s})(y:ι → Cover)(s:ι):
    placed X L y {s}=tuftV (L s) (shifted (X s) (y s)):=singleton _ _

theorem quiet (X:ι → Era G ℝ)(L:(s:ι) → ℝ →L[ℝ] Pen D {s})(y:ι → Cover):placed X L y ∅=0:=
  other _ (by simp)

theorem qualified (X:ι → Era G ℝ)(L:(s:ι) → ℝ →L[ℝ] Pen D {s})(y:ι → Cover)
    (each:∀s,Auth (k s) (X s)):Eu k (placed X L y):=legal _ (fun s=>((each s).shifted (y s)).tuft (L s))

theorem priced [DecidableEq ι](X:ι → Era G ℝ)(L:(s:ι) → ℝ →L[ℝ] Pen D {s})(y:ι → Cover)(n:Side)
    (e r:ℕ)(b:ℝ)(a:ι → ℝ)
    (each:∀s,MarkU y {s} ((shifted (X s) (y s)).1 n e r) ((shifted (X s) (y s)).2 e r) b (a s))
    (s:ι):MarkU y {s} ((placed X L y {s}).1 n e r) ((placed X L y {s}).2 e r) b (‖L s‖*a s):=by
  rw [field]
  exact through (L s) (each s)

end YM.Integration.WilsonPointChildPlacedFamily
