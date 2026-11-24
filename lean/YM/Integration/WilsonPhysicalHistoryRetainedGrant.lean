import YM.Integration.WilsonPhysicalHistoryRetainedProduct
import YM.Integration.WilsonFundedWindowCompany

/-! Use the physical charter and original houses of the receiving spring to
pay every retained regular Mayer letter at once on its own affine sample. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open ConnectedActivityE6 ConnectedActivityE6.Coat
open Bloch Laurent Push Push.AbsoluteSums Precision Exterior Shell Channel
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Opera
open scoped BigOperators Classical Topology
variable {G : Gauge}

private theorem cap {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
    {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W t μ C : ℝ} {o : Target.Order G W}
    {B : Rep G f} (H : Cash W t μ L Q o C T B)
    (room : Q.goal L t≤1/4) (X : Coat T F) (clock : X.x=t) (width : X.width=o.K)
    (manifest : X.manifest) (l : Finset ℕ) (m : ℕ) (z : Air f G) (i : ℕ) :
    |X.vertex B Q.table W o.a l m z (regularHead S i)|≤1/4 := by
  let a : LogIndex c f:=.inl (.inl i)
  have base:=H.fares.atom (by unfold Target.relative; linarith [Q.usable,Q.bound,Q.pos])
    Q.usable.le (Sum.inr (Sum.inl a)) (exChart S T B (radiusB t) Q.halo a)
  have money : H.w a≤Q.goal L t := base
  exact ((H.quotes F X clock width manifest).2.1 a z).2.trans (money.trans room)

private theorem actual (R : Run G) {N n m : ℕ} (hm : m<N) :
    Nonempty (Guide R.alloy.B R.kit.shape N m n (R.family.path.rep N n (m+1))) := by
  let D:=ActualRunSpring.selected R N n m hm
  rw [D.fine]
  exact ⟨D.spring.H.houses D.point⟩

theorem affine_quarter (R : Run G) (simple : G.Simple)
    (held : WilsonFundedWindowCompany.PhysicalInputs R.kit) :
    ∀ᶠ m : ℕ in atTop, ∀ (N n : ℕ), m<N →
      let k:=R.alloy.B.a.clock.J (m+1)
      let j:=R.alloy.B.a.clock.J m
      let P:=R.family.path.rep N n (m+1)
      let T:=Pressure.Testing.ships R.alloy.B N m n
      ∃ _H : Guide R.alloy.B R.kit.shape N m n P,
        ∀ {F : Forest (R.alloy.B.a.clock.op m n).ratio} (X : Coat T F),
          X.x=R.alloy.B.a.clock.hatBeta m → X.width=(R.kit.shape.o k j).K → X.manifest →
          ∀ (l : Finset ℕ) (w : ℕ) (z : Air (R.family.side (m+1) n) G) (i : ℕ),
            |X.vertex P (R.kit.target k j).table (R.kit.walls k j) (R.kit.shape.o k j).a l w z
              (regularHead (R.alloy.B.a.clock.op m n) i)|≤1/4 := by
  let A:=R.alloy.B.a
  have rise : Tendsto A.clock.hatBeta atTop atTop :=
    tendsto_atTop_add_const_left _ _ (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  have next := rise.comp (tendsto_add_atTop_nat 1)
  have low := (tendsto_rpow_neg_atTop (show (0:ℝ)<7/16 by norm_num)).comp next
  filter_upwards [low.eventually (gt_mem_nhds (show (0:ℝ)<1/4 by norm_num)),
    next.eventually_ge_atTop 1] with m price one
  dsimp only
  intro N n below
  let k:=A.clock.J (m+1)
  let j:=A.clock.J m
  obtain ⟨H⟩:=actual R (N:=N) (n:=n) below
  use H
  intro F X clock width manifest l w z i
  apply cap H _ X clock width manifest l w z i
  change (Pressure.betaF G (A.clock.hatBeta m) (R.rolls.L k))^(R.kit.target k j).rate ≤ 1/4
  rw [←PriceCompiler.beta_eq R.alloy.B.valid m]
  refine (Real.rpow_le_rpow_of_exponent_le one ?_).trans price.le
  have e := (R.kit.expense k j).reach
  rw [(held.1 k j).2.2.2.1] at e
  exact e.le

end YM.Integration.OriginalMarkedRunAction
