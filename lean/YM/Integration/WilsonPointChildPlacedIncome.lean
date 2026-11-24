import YM.Integration.WilsonPointChildPlacedFamily
import YM.Integration.WilsonVacuumPreResetMarkedFiledAtRun
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildPlacedIncome
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
open WilsonPointChildPlacedFamily
open WilsonVacuumPreResetMarkedOrdinaryBound (weights)
open private rooted from YM.Integration.WilsonPointChildWindingRoot

variable {G:Gauge}{ι:Type}{r:ℕ}{D:ι  →  ℕ}

theorem transported {V:Type} [NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]
    (L:ℝ  →L[ℝ] V)(X:Era G ℝ)(z:Cover)(n:Side)(e r:ℕ){w A C τ:ℝ}(ww:0<w)
    (salary:Wig terrain (fun _:Unit=>0) w A {()} (X.2 e r))
    (fold:∀x,|plume (X.2 e r) n x| ≤ A)
    (gap:∀x,|X.1 n e r x-plume (X.2 e r) n x| ≤ C*τ):
    let T:=tuftV L (shifted X z)
    ∀x,‖(remade T).1 n e r x‖ ≤ ‖L‖*A ∧ ‖T.1 n e r x-(remade T).1 n e r x‖ ≤ (‖L‖*C)*τ:=by
  intro T x
  let y:=jog (-wrap n z) ∘ x
  have wC:=Cork.turn z (rooted ww.le salary)
  have changed:plume (T.2 e r) n=L ∘ revolve (wrap n z) (plume (X.2 e r) n):=
    (plume_map _ wC ww L n).trans (congrArg (fun F=>L ∘ F) (plume_shift z n))
  change ‖plume (T.2 e r) n x‖ ≤ _ ∧ ‖L (X.1 n e r y)-plume (T.2 e r) n x‖ ≤ _
  rw [changed]
  change ‖L (plume (X.2 e r) n y)‖ ≤ _ ∧ ‖L (X.1 n e r y)-L (plume (X.2 e r) n y)‖ ≤ _
  rw [←map_sub,mul_assoc]
  exact ⟨(L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (fold y) (norm_nonneg L)),
    (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (gap y) (norm_nonneg L))⟩

def sources (R:Run G)(u:ι  →  G.ColorIndex){k h:ι  →  ℕ}(depth:∀s,k s<h s)(N m:ℕ)
    (v:(s:ι)  →  Letter (R.family.labels.level (k s)))(p:(s:ι)  →  Scroll (h s)):
    ι  →  Era G ℝ:=fun s=>ledger R (u s) (depth s) N (N-m) m (v s) (p s)

def salary (R:Run G)(m:ℕ)(η:ℝ){h:ι  →  ℕ}(p:(s:ι)  →  Scroll (h s))
    (cut:(s:ι)  →  ℝ  →L[ℝ] Pen D {s})(s:ι):ℝ:=
  (1+‖cut s‖)*((R.family.path.levels.clock.hatBeta m)^η*‖physical (p s)‖+(1+‖physical (p s)‖))

theorem original [Fintype ι](R:Run G)(simple:G.Simple)(booked:WilsonPointChildFiledTest.Filed R)
    (enrolled:WilsonPointChildWindingHierarchy.Filed R)(paid:WilsonPointChildWindingSchool.Paid R.kit)
    (u:ι  →  G.ColorIndex){k h:ι  →  ℕ}(depth:∀s,k s<h s)(o:Loc G 1)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (E:ℕ){η:ℝ}(positive:0<η):
    ∀ᶠm:ℕ in atTop,∀N per,m ≤ N  →  ∀(v:(s:ι)  →  Letter (R.family.labels.level (k s)))(p:(s:ι)  →  Scroll (h s))
      (y:ι  →  Cover)(cut:(s:ι)  →  ℝ  →L[ℝ] Pen D {s}),
      let X:=sources R u depth N m v p
      let K:=placed X cut y
      let n:=R.family.side m per
      let fee:=salary R m η p cut
      Eu k K ∧ K ∅=0 ∧ (∀s,0<fee s) ∧ ∀J,∀e ≤ E,∀r x,
        ‖(repaint K J).1 n e r x‖ ≤ weights fee J ∧
        ‖(K J).1 n e r x-(repaint K J).1 n e r x‖ ≤ rate R.family.path.levels m per*weights fee J:=by
  let A:=R.family.path.levels
  have dry(s:ι):=WilsonPointChildWindingIncome.original R simple booked (u s) (depth s) o tags (fare G) paid E positive
  have close(s:ι):=enrolled (u s) (k s) E (h s) (depth s) o tags
  filter_upwards [eventually_all.mpr dry,eventually_all.mpr close,(WardBin.bell A simple).eventually_ge_atTop 1] with m priced received fund N per live v p y cut X K n fee
  have hp:0 ≤ (A.clock.hatBeta m)^η:=(Real.rpow_pos_of_pos (zero_lt_one.trans_le fund) η).le
  have fp(s:ι):0<fee s:=by
    change 0<(1+‖cut s‖)*((A.clock.hatBeta m)^η*‖physical (p s)‖+(1+‖physical (p s)‖))
    have h':=hp
    positivity
  refine ⟨qualified X cut y (fun s=>(priced s N live (v s) (p s)).1),quiet X cut y,fp,?_⟩
  intro J e he r x
  have τ:0 ≤ rate A m per:=(Real.exp_pos _).le
  by_cases single:J.card=1
  · obtain ⟨s,rfl⟩:=card_eq_one.mp single
    have bound:=((priced s N live (v s) (p s)).2 e he r)
    have run:=WilsonPointChildPairedHistory.original R (u s) (depth s) tags simple o (fare G) paid N (N-m) m (by omega) (v s) (p s)
    have δ:(∀x,|(X s).1 n e r x-plume ((X s).2 e r) n x| ≤ (1+‖physical (p s)‖)*rate A m per):=by
      change ∀x,|(ledger R (u s) (depth s) N (N-m) m (v s) (p s)).1 n e r x-plume ((ledger R (u s) (depth s) N (N-m) m (v s) (p s)).2 e r) n x| ≤ _
      rw [run.1 n,run.2]
      exact received s N per live (v s) (p s) e he r
    have amt:=transported (cut s) (X s) (y s) n e r ((Primer.FamilyWindow R.family).pos (A.clock.J m)) bound.1 (bound.2 n) δ x
    change ‖(remade (placed X cut y {s})).1 n e r x‖ ≤ _ ∧ ‖(placed X cut y {s}).1 n e r x-(remade (placed X cut y {s})).1 n e r x‖ ≤ _
    rw [field]
    simp only [weights,prod_singleton]
    let g:=(A.clock.hatBeta m)^η*‖physical (p s)‖
    let c:=1+‖physical (p s)‖
    have gp:0 ≤ g:=mul_nonneg hp (norm_nonneg _)
    have cp:0 ≤ c:=by dsimp [c];positivity
    have h₀:‖cut s‖*g ≤ fee s:=mul_le_mul (by linarith) (le_add_of_nonneg_right cp) gp (by positivity)
    have h₁:‖cut s‖*c ≤ fee s:=mul_le_mul (by linarith) (le_add_of_nonneg_left gp) cp (by positivity)
    exact ⟨amt.1.trans h₀,amt.2.trans ((mul_le_mul_of_nonneg_right h₁ τ).trans_eq (mul_comm ..))⟩
  have gone:K J=0:=other _ single
  change ‖(remade (K J)).1 n e r x‖ ≤ _ ∧ ‖(K J).1 n e r x-(remade (K J)).1 n e r x‖ ≤ _
  rw [gone,remake_zero]
  have cost:0 ≤ weights fee J:=Finset.prod_nonneg (fun s _=>(fp s).le)
  simpa only [Prod.fst_zero,Pi.zero_apply,sub_zero,norm_zero] using And.intro cost (mul_nonneg τ cost)

end YM.Integration.WilsonPointChildPlacedIncome
