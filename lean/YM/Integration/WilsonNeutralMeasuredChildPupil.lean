import YM.Integration.WilsonNeutralPhysicalCoverCopies
import YM.Integration.WilsonOriginalReceivedCopiedCover

/-! Comparison at the original stored pupil, its own physical reporting
side, and the one filed, independently placed child. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonNeutralMeasuredChildPupil
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open scoped Classical BigOperators Topology

section Measured
variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m ≤ i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) {V : Type} [Fintype V] [DecidableEq V]
  {X : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical)


local notation "tape" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "cash" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter

open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonRunFormalMarkedStep WilsonNeutralNormalizedForestStep
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle
open scoped Topology BigOperators Matrix Classical

open AllOrder.Ker


variable {d Df:ℕ} (wood:Primer.Families R.family) (color:hue G) (depth:d<Df)
  {U:ℕ→ℕ}(grant:WilsonWindowFormalPurchase.Canonical U R.kit)

local notation "grid" => R.family.side i per
local notation "V₀" => R.family.path.levels
local notation "clock₀" => R.family.path.levels.clock
local notation "copies" => Covers R.family.path.levels.S i grid
local notation "A₀" => destination R.family.path.levels N i

include course grant in
theorem paired (hs:G.Simple)(o:Loc G 1)(hd:d≤(V₀).clock.J (i+1))
    (F:∀c:copies,Forest ((V₀).clock.op i c.val).ratio)(tag:∀c:copies,((V₀).clock.op i c.val).Choices)
    (F':∀c:copies,Forest (Flat.primary (A₀).patch (V₀).clock.kernel (R.family.side i c.val)).ratio)
    (u:∀c:copies,(Flat.primary (A₀).patch (V₀).clock.kernel (R.family.side i c.val)).Choices)
    (b:Letter (R.family.labels.level d))(f:Studio Df)(z:Site (grid*(A₀).L))
    (arm:Wallet actors)(s:Multi.Hot (Stock.census V))(scale:ℂ)
    (j:ℕ)(hj:j≤order)(B:Stationary.Link G grid):
    let r:Ratio grid (grid*(A₀).L):=Ratio.mk (A₀).L rfl
    let w:=Primer.densityCoeff R.family wood color N (i+1)
    let Y:=Primer.fieldCoeffs R.family color wood depth N (i+1) b f
    let lower:=Kemp.braise A₀ (wood i) w (Kemp.work (lift (r.residue z)) Y) R.metals.O ((V₀).blocks i 0).branches d
    let value:=MvPolynomial.eval (FreeResolvent.flatten (Stationary.arm G grid 1 B) ∘ Lotus.tint (r.parent z))
      (coeff j (Kemp.banner d lower grid))
    Tendsto (fun c:copies=>
      (FVA1Physical.TwoReset.FkCover R cut (π (i+1)) tape order P.model grades arm grid dvd_rfl F tag B j c).part s.val -
        scale*(WilsonNeutralPhysicalCoverCopies.phase R wood color depth N i grid (R.family.side i c.val) c.prop
          (F' c) (u c) b f z j B:ℝ))
      (coverFilter (V₀).S i grid) (𝓝 ((peek dvd_rfl student grades (π (i+1)) tape arm j B).part s.val-scale*value)):=by
  intro r w Y lower value
  have original:=WilsonOriginalReceivedCopiedCover.published R hk D Q π Γ Ψ course books hi cut ahead actors pieces
    grades order shelf seats physical P
  have measured:=original arm grid dvd_rfl F tag B j hj
  have projection:=((Poly.part_cont s.val).tendsto _).comp measured
  have numerical:=WilsonNeutralPhysicalCoverCopies.original R wood color depth grant N i hs o cut hd grid
    F' u b f z j B
  exact projection.sub (tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp numerical))

include course grant in
theorem fixed (hs:G.Simple)(o:Loc G 1)(hd:d≤(V₀).clock.J (i+1))
    (F:∀c:copies,Forest ((V₀).clock.op i c.val).ratio)(tag:∀c:copies,((V₀).clock.op i c.val).Choices)
    (F':∀c:copies,Forest (Flat.primary (A₀).patch (V₀).clock.kernel (R.family.side i c.val)).ratio)
    (u:∀c:copies,(Flat.primary (A₀).patch (V₀).clock.kernel (R.family.side i c.val)).Choices)
    (b:Letter (R.family.labels.level d))(f:Studio Df)(z:Site (grid*(A₀).L))
    (arm:Wallet actors)(s:Multi.Hot (Stock.census V))(scale:ℂ)
    (j:ℕ)(hj:j≤order)(B:Stationary.Link G grid)
    (finite:∀ᶠ c:copies in coverFilter (V₀).S i grid,
      (FVA1Physical.TwoReset.FkCover R cut (π (i+1)) tape order P.model grades arm grid dvd_rfl F tag B j c).part s.val =
        scale*(WilsonNeutralPhysicalCoverCopies.phase R wood color depth N i grid (R.family.side i c.val) c.prop
          (F' c) (u c) b f z j B:ℝ)):
    let r:Ratio grid (grid*(A₀).L):=Ratio.mk (A₀).L rfl
    let w:=Primer.densityCoeff R.family wood color N (i+1)
    let Y:=Primer.fieldCoeffs R.family color wood depth N (i+1) b f
    let lower:=Kemp.braise A₀ (wood i) w (Kemp.work (lift (r.residue z)) Y) R.metals.O ((V₀).blocks i 0).branches d
    (peek dvd_rfl student grades (π (i+1)) tape arm j B).part s.val=scale*
      (MvPolynomial.eval (FreeResolvent.flatten (Stationary.arm G grid 1 B) ∘ Lotus.tint (r.parent z))
        (coeff j (Kemp.banner d lower grid)):ℝ):=by
  intro r w Y lower
  have pairedRead:=paired R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades order shelf seats
    physical P wood color depth grant hs o hd F tag F' u b f z arm s scale j hj B
  haveI:NeBot (coverFilter (V₀).S i grid):=coverFilter_neBot R.kit.floor _ _
  apply sub_eq_zero.mp
  apply tendsto_nhds_unique pairedRead
  apply tendsto_const_nhds.congr'
  filter_upwards [finite] with c hc
  rw [hc,sub_self]

end Measured
end YM.Integration.WilsonNeutralMeasuredChildPupil
end
