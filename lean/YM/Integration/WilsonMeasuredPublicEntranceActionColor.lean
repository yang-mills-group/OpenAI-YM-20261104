import YM.Integration.WilsonMeasuredPublicEntranceRegisteredColor
import YM.Integration.WilsonMeasuredPublicEntrancePositiveRay
import YM.Integration.WilsonMeasuredSignedActionDirection

/-! The original six-term action need only be identified on its nonnegative
ray modulo the measured identity. The true reflected form fixes its scale. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceActionColor
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Stab Next.Rank OJoint
open WilsonMeasuredPublicEntranceMarkedQuadratics WilsonMeasuredPublicEntranceQuadraticFiled
open WilsonMeasuredPublicEntranceCommonColor (carried)
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

abbrev field (C:Family G){d:ℕ}(hd:4≤d):((Bel C.book).Field d):=
  (scheme C.labels).rise hd (stepField C)

theorem signed (C:Family G){d:ℕ}(hd:4≤d):
    (2:ℝ)•(fields C.labels d) (field C hd)=marked G hd 1:=by
  have posted:(fields C.labels d) (field C hd)=seat hd ((fields C.labels 4) (stepField C)):=by
    apply Subtype.ext
    change address C.labels d ((scheme C.labels).rise hd (stepField C)) =
      ((fields C.labels 4) (stepField C)).val
    rw [address_rise]
    rfl
  rw [posted,←folded,←WilsonMeasuredSignedActionDirection.direct C]
  exact ((seat hd (G:=G)).restrictScalars ℝ).map_smul (2:ℝ) _ |>.symm

theorem transfer {d:ℕ}(hd:4≤d)(Z:Module.End ℂ (D d))(fixed:Z (field C hd)=field C hd):
    carried C Z (marked G hd 1)=marked G hd 1:=by
  let U:=fields C.labels d
  let T:=carried C Z
  rw [←signed C hd]
  change T ((2:ℝ) • (U (field C hd)))=(2:ℝ) • U (field C hd)
  have eq:T (U (field C hd))=U (field C hd):=by
    change U (Z (U.symm (U (field C hd))))=_
    rw [U.symm_apply_apply,fixed]
  exact ((T.restrictScalars ℝ).map_smul (2:ℝ) _).trans (congrArg ((2:ℝ) • ·) eq)

theorem original (F:Final C f S)(J:ℝ→tower S)(lead:Leading F J)(simple:G.Simple)
    {d:ℕ}(hd:6≤d){I:Type*}{l:Filter I}[NeBot l]{r t:I→ℝ}
    (hr:Tendsto r l trail){u:ℝ}(hu:0<u)(ht:Tendsto t l (𝓝 u))(pos:∀i,0<t i)
    (Z:Module.End ℂ (D d))
    (conv:∀v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) v) l (𝓝 (Z v)))
    (action:∃s:ℝ,0 ≤ s ∧ ∃k:ℂ,Z (field C (by omega:4≤d))=
      (s:ℂ) • field C (by omega)+k • (Bel C.book).unit d):
    ∃c:Knight G,(conn c 1 ∨ conn c (-1)) ∧ ∀v:D d,
      records G d (fields C.labels d (Z v))=changing c (records G d (fields C.labels d v)):=by
  obtain ⟨s,hs,k,receipt⟩:=action
  have owns:=WilsonMeasuredPublicEntrancePositiveRay.original F J lead hr hu ht pos Z conv
    (field C (by omega:4≤d)) hs receipt
  exact WilsonMeasuredPublicEntranceRegisteredColor.original F J lead simple hd hr hu ht pos Z conv
    (transfer (by omega) Z owns)
end YM.Integration.WilsonMeasuredPublicEntranceActionColor

