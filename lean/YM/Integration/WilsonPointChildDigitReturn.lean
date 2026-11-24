import YM.Integration.WilsonPointChildCoverReturn
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildDigitReturn
open YM FormalBulk08 Lattice RG Laurent Next.Foundations PhysicalNext.Repeat.Legato
open Reef Flat Stationary Dawn Pose Kemp Palm Shore Mesa Wine Quire Roof Lotus Sierra Gorge Dove Rial
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Embroider
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped ContDiff BigOperators Topology Classical
variable {G:Gauge}{d D:ℕ}

private theorem same_program (R:Run G)(u:G.ColorIndex)(N j d:ℕ)(Z:Mesa.Pot G):
    Sierra.enterStep (Next.Free.destination R.family.path.levels N j) (routes R j)
      (WilsonNeutralPointCourse.quiet R (routes R) u N (j+1)) u R.metals.O
      (WilsonNeutralPointCourse.branches R j) d Z=WilsonMarkedCoverIndependentStep.fixed R u N j d Z:=rfl

/-- All links, the test and its anchor undergo the same selected single-child translation. -/
theorem dated (R:Run G)(digit:∀ i,Site (R.family.S.block i))(u:G.ColorIndex)(N j:ℕ)
    (Y:Plaza (R.family.labels.level d) D)(v:Letter (R.family.labels.level d))(p:Scroll D):
    let P:=WilsonCoeffUV.loose R.family.path.levels j
    WilsonNeutralPointCourse.forward R (routes R) u digit N j Y v (physical p)=
      (P.L.val:ℝ)^d • WilsonMarkedCoverIndependentStep.fixed R u N j d
        (Kemp.work (lift (digit j)) (Y v (physical (growWord P (digit j) D p)))):=by
  intro P
  dsimp only [WilsonNeutralPointCourse.forward,Function.comp_apply,WilsonNeutralPointMatrix.child,
    Kemp.stepsong]
  rw [same_program]
  have eq:=WilsonPointChildCoverStep.pulled P (digit j) (Elm.growL R.family.path.levels j) p
  exact congrArg (fun f:Dawn.Studio D=>(P.L.val:ℝ)^d • WilsonMarkedCoverIndependentStep.fixed R u N j d
    (Kemp.work (lift (digit j)) (Y v f))) eq

/-- The complete dated matrix acts on the one genuine child, with its original
test pullback, its prescribed upper vacuum and its kinetic reversion. -/
theorem normalized (R:Run G)(u:G.ColorIndex)(depth:d<D)(digit:∀ i,Site (R.family.S.block i))(N j:ℕ)(simple:G.Simple)
    (o:Loc G 1)(live:j<N)(front:d≤R.family.path.levels.clock.J (j+1))
    (v:Letter (R.family.labels.level d))(p:Scroll D):
    let P:=WilsonCoeffUV.loose R.family.path.levels j
    let Y:=WilsonNeutralPointCourse.filed R (routes R) u depth digit N
    let T:=WilsonNeutralPointCourse.transfer R (routes R) u depth digit N j
    Y j v (physical p)=∑s,surf ((T⁻¹) s v)
      ((P.L.val:ℝ)^d • WilsonMarkedCoverIndependentStep.fixed R u N j d
        (Kemp.work (lift (digit j)) (Y (j+1) s (physical (growWord P (digit j) D p))))):=by
  intro P Y T
  let H:=forward R (routes R) u digit N j (Y (j+1))
  obtain ⟨mat,eqn⟩:=received R (routes R) u depth digit N j simple o live front
  have put:larch H T⁻¹=Y j:=by
    change larch (forward R _ _ _ _ _ _) _=_
    rw [←eqn,larch_circuit,Matrix.mul_nonsing_inv _ mat.det,larch_unit]
  have same:=congrFun (congrFun put v) (physical p)
  rw [←same]
  simp only [larch, Finset.sum_apply, Kemp.launch, H, dated]
  rfl

/-- Direct cover program on the original scroll. Each edge is contracted on
its own site and the entire inverse matrix is applied after that contraction. -/
def table (R:Run G)(u:G.ColorIndex)(depth:d<D)(digit:∀ i,Site (R.family.S.block i))(N:ℕ):
    ℕ→ℕ→Letter (R.family.labels.level d)→Scroll D→Pot G
  | 0, _, v, p =>(sectionY (R.family.localSection d) depth) v (physical p)
  | h+1, j, v, p =>
    let P:=WilsonCoeffUV.loose R.family.path.levels j
    let T:=WilsonNeutralPointCourse.transfer R (routes R) u depth digit N j
    ∑s,surf ((T⁻¹) s v) ((P.L.val:ℝ)^d • WilsonMarkedCoverIndependentStep.fixed R u N j d
      (Kemp.work (lift (digit j)) (table R u depth digit N h (j+1) s (growWord P (digit j) D p))))

theorem original (R:Run G)(u:G.ColorIndex)(depth:d<D)(digit:∀ i,Site (R.family.S.block i))(simple:G.Simple)(o:Loc G 1)
    (N h j:ℕ)(age:j+h=N)(enrolled:∀i:ℕ,j ≤ i → i < N → d ≤ R.family.path.levels.clock.J (i+1))
    (v:Letter (R.family.labels.level d))(p:Scroll D):
    table R u depth digit N h j v p=WilsonNeutralPointCourse.filed R (routes R) u depth digit N j v (physical p):=by
  induction h generalizing j v p with
  | zero=>have hj:j=N:=by omega
          subst j
          simp [table,WilsonNeutralPointCourse.filed,WilsonNeutralPointCourse.walk]
  | succ h ih=>
    rw [normalized R u depth digit N j simple o (by omega) (enrolled j le_rfl (by omega))]
    change (∑s,surf _ (_ • WilsonMarkedCoverIndependentStep.fixed _ _ _ _ _
      (Kemp.work (lift (digit j)) (table R u depth digit N h (j+1) s _))))=_
    apply Finset.sum_congr rfl
    intro s hs
    rw [ih (j+1) (by omega) (fun i hi hiN=>enrolled i (by omega) hiN)]

end YM.Integration.WilsonPointChildDigitReturn
