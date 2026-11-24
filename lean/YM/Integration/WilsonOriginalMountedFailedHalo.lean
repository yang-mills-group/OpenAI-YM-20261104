import YM.Integration.WilsonOriginalFailedFaceCalendar
import YM.Integration.WilsonOriginalMountedOrder

/-! The paid failed-halo term at the earlier original flat and ClockFace fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMountedFailedHalo
open Function Filter Finset Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open WilsonOriginalMountedRegular WilsonOriginalMountedOrder
open Next.Rank.Spindle Next.Rank.Perch Stationary Exterior RG17 Pressure Pert.Asymptotics
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G)(simple:G.Simple)

def board (N per b:ℕ)(U:Config G (R.family.side b per)):Prop:= U=1 ∨
  ∃(d:ℕ)(face:ClockFace R d b N per)(a:(R.family.labels.level d).Index),
    U=net (R.family.path.rep N per b).p 0 (sizeQ R.family b) (face.tiles a).val

local notation "spring" b:max N:max per:max U:max =>
  WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op b per) (R.family.path.β N per (b+1)) U

include simple in
theorem received:∀ᶠ b:ℕ in atTop,∀{N per:ℕ}(_live:b<N)(U:Config G (R.family.side b per)),
    board R N per b U → (Real.exp (spring b N per U))^2 ≤ 2:=by
  filter_upwards [WilsonOriginalClockFacePosterior.original R simple] with b tiles N per live U which
  rcases which with rfl|⟨d,face,a,rfl⟩
  · norm_num [WilsonOriginalDecoderSpring.bill]
  · exact tiles live face a

variable (n:ℕ){A tol:ℝ}(ap:0 ≤ A)(tp:0 ≤ tol)

def first:ℕ:=(eventually_atTop.mp (WilsonOriginalFailedFaceCalendar.original R simple n ap tp)).choose

variable {m k b i N per:ℕ}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    {Ψ:∀j,RG.Rep G (R.family.side j per)}(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (mb:m ≤ b)(bi:b ≤ i)(live:i < N){V:Type}[Fintype V][DecidableEq V]{J:Census V}{s:J.Mode}
    {row:WilsonOriginalOccupiedWindow.Slice R J (Ψ i)}{target:Config G (R.family.side i per)→Poly J}
    (F:Filing R (Ψ i) row target s)
    (fixed:(R.family.path.levels.budget i).supportExponent ≤ 100)(count:s.val.card ≤ n)
    (crop:F.h ≤ Nat.ceil (A*(1+Real.log (regulatorRun R.family N per b)⁻¹)))
    (P D p:ℕ)(order:P+D*width s+2 ≤ p)(U:Config G (R.family.side b per))
local notation "H" => R.family.path.levels.clock.hatBeta i
local notation "g" => regulatorRun R.family N per b

include course mb bi live fixed count crop order in
theorem atSpring (late:first R simple n ap tp ≤ b)(tilt:(Real.exp (spring b N per U))^2 ≤ 2):
    event F b tol (H) (spring b N per U) p ≤ (g)^(P+D*width s):=by
  have point:(Ψ i).p=R.family.path.levels.budget i:=(course.1.walk i (mb.trans bi) live.le).truep.point
  have size:(Ψ i).p.B=Nat.ceil ((Real.log (H))^2):=by rw [point];rfl
  have α:(Ψ i).p.supportExponent ≤ 100:=by rw [point];exact fixed
  unfold event
  dsimp only
  split_ifs
  · exact pow_nonneg (IterationFour.Currency.g_pos R.makes N per b (bi.trans live.le)).le _
  · exact (eventually_atTop.mp (WilsonOriginalFailedFaceCalendar.original R simple n ap tp)).choose_spec
      b late bi live.le size α count crop (sq_nonneg _) tilt order

include course mb bi live fixed count crop order in
theorem original (late:first R simple n ap tp ≤ b)
    (opening:(eventually_atTop.mp (received R simple)).choose ≤ b)(node:board R N per b U):
    event F b tol (H) (spring b N per U) p ≤ (g)^(P+D*width s):=by
  exact atSpring R simple n ap tp course mb bi live F fixed count crop P D p order U late
    ((eventually_atTop.mp (received R simple)).choose_spec b opening (bi.trans_lt live) U node)

end YM.Integration.WilsonOriginalMountedFailedHalo
end
