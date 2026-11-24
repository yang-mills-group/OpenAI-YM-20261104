import YM.Integration.WilsonPointChildCoverStep
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildCoverReturn
open YM FormalBulk08 Lattice RG Laurent Next.Foundations PhysicalNext.Repeat.Legato
open Reef Flat Stationary Dawn Pose Kemp Palm Shore Mesa Wine Quire Roof Lotus Sierra Gorge Dove Rial
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Embroider
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped ContDiff BigOperators Topology Classical
variable {G:Gauge}{d D:ℕ}

/-- The complete dated matrix acts on the one genuine child, with its original
test pullback, its prescribed upper vacuum and its kinetic reversion. -/
theorem normalized (R:Run G)(u:G.ColorIndex)(depth:d<D)(N j:ℕ)(simple:G.Simple)
    (o:Loc G 1)(live:j<N)(front:d≤R.family.path.levels.clock.J (j+1))
    (v:Letter (R.family.labels.level d))(p:Scroll D):
    let P:=WilsonCoeffUV.loose R.family.path.levels j
    let Y:=WilsonNeutralPointCourse.filed R (routes R) u depth (fun _=>0) N
    let T:=WilsonNeutralPointCourse.transfer R (routes R) u depth (fun _=>0) N j
    Y j v (physical p)=∑s,surf ((T⁻¹) s v)
      ((P.L.val:ℝ)^d • WilsonMarkedCoverIndependentStep.fixed R u N j d
        (Y (j+1) s (physical (growWord P 0 D p)))):=by
  intro P Y T
  let H:=forward R (routes R) u (fun _=>0) N j (Y (j+1))
  obtain ⟨mat,eqn⟩:=received R (routes R) u depth (fun _=>0) N j simple o live front
  have put:larch H T⁻¹=Y j:=by
    change larch (forward R _ _ _ _ _ _) _=_
    rw [←eqn,larch_circuit,Matrix.mul_nonsing_inv _ mat.det,larch_unit]
  have same:=congrFun (congrFun put v) (physical p)
  rw [←same]
  simp only [larch, Finset.sum_apply, Kemp.launch, H, WilsonPointChildCoverStep.filed]
  rfl

/-- Direct cover program on the original scroll. Each edge is contracted on
its own site and the entire inverse matrix is applied after that contraction. -/
def table (R:Run G)(u:G.ColorIndex)(depth:d<D)(N:ℕ):
    ℕ→ℕ→Letter (R.family.labels.level d)→Scroll D→Pot G
  | 0, _, v, p =>(sectionY (R.family.localSection d) depth) v (physical p)
  | h+1, j, v, p =>
    let P:=WilsonCoeffUV.loose R.family.path.levels j
    let T:=WilsonNeutralPointCourse.transfer R (routes R) u depth (fun _=>0) N j
    ∑s,surf ((T⁻¹) s v) ((P.L.val:ℝ)^d • WilsonMarkedCoverIndependentStep.fixed R u N j d
      (table R u depth N h (j+1) s (growWord P 0 D p)))

theorem original (R:Run G)(u:G.ColorIndex)(depth:d<D)(simple:G.Simple)(o:Loc G 1)
    (N h j:ℕ)(age:j+h=N)(enrolled:∀i:ℕ,j ≤ i → i < N → d ≤ R.family.path.levels.clock.J (i+1))
    (v:Letter (R.family.labels.level d))(p:Scroll D):
    table R u depth N h j v p=WilsonNeutralPointCourse.filed R (routes R) u depth (fun _=>0) N j v (physical p):=by
  induction h generalizing j v p with
  | zero=>have hj:j=N:=by omega
          subst j
          simp [table,WilsonNeutralPointCourse.filed,WilsonNeutralPointCourse.walk]
  | succ h ih=>
    rw [normalized R u depth N j simple o (by omega) (enrolled j le_rfl (by omega))]
    change (∑s,surf _ (_ • WilsonMarkedCoverIndependentStep.fixed _ _ _ _ _
      (table R u depth N h (j+1) s _)))=_
    apply Finset.sum_congr rfl
    intro s hs
    rw [ih (j+1) (by omega) (fun i hi hiN=>enrolled i (by omega) hiN)]

end YM.Integration.WilsonPointChildCoverReturn
