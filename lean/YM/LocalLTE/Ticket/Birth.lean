import YM.LocalLTE.Ticket.Prize
/-!
## Canonical berth at true IN History.FULL cap for this initial E-location and λ-free.K shelf!

Lens.Probe not limited to taps later, use any inlets from Grouped Iter.
Adapt genuine `summon` method on current trajectory by additionally manipulating
the costs on the private glazed copy. This is explicit kernel convergence on raw.Even where bad.No
comparison with other Family witnesses/shifted root.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Ticket
open Function Filter Set Lattice Wilson RG Source Labels Extra.Histories Bid
open LocalLTE.Vinca LocalLTE.FrameBox AnalyticBridge VerifiedReset Collection Price PhysicalNext.Repeat Blush
open Push Local Planned.GuardedAtom LocalLTE.River YM.MergeProof
open Finset MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{H:History G}{N m p:ℕ}{k d:ℕ}{F:Labels.Frame G d}
variable {n:Side} (B:SectionData F)(A:Hol G)
open Guard
-- adapt demo, purely for pricing private, restore exact real ForceCost afterwards.
private def glazed (A : Activities G n) : Activities G n := { A with
  forced := fun i => {A.forced i with extraTest:=fun _ => True} }
private def plate (R : Rep G n) : Rep G n := {R with activities:=glazed R.activities}
private def demo {P:BudgetPoint}{A:Activities G n}{K : Keeper P A} (hs : ∀ s,A.K (K.code s)=0) : Shelf (glazed A) := ⟨K.code,K.support,K.inventory,fun _ _ => trivial,hs⟩
-- The following proves preserving literal.PL.
variable (K:Guard.Keeper (H.rep N p N).p (H.rep N p N).activities) (hs:∀ s,(H.rep N p N).activities.K (K.code s)=0)
    (q:ℕ)(h: H.Selected)
local notation "Z" => summit F B H N p K hs q
local notation "Y"=> H.rep N p N
local notation "T"=> Ticket.plate Y
-- Actual cap
local notation "v0"=> H.levels.clock.forcedAllowance N
variable {C c:ℝ}(hS:B.Sound A)(hC:1 ≤ C)(ht:∀ (i:F.Index)(U: Config G (H.S.side N p)),‖B.places (Size.axis F i) 0 U‖ ≤ C)
    (hp: Extra.Histories.fee F (H.levels.budget N) (B.footprint (0:Site (H.S.side N p))) C (H.levels.clock.forcedAllowance N)≤ Real.sqrt (H.levels.clock.forcedAllowance N)*c) (hf:0≤c)
include h hS hC ht hp hf
lemma vault (v:F.Coeff) : Local.ForceCost ((H.rep N p N).p) ((H.rep N p N).activities) (((Z).plays v).forced) (Real.sqrt (H.levels.clock.forcedAllowance N)*(c* F.coeffSize v)):=by
    let Y':= H.rep N p N; let K':=T; let X:= B.footprint (0:Site (H.S.side N p)); let u:= Extra.Histories.supplement B K' 0 v
    have hβ:K'.activities.KBound K'.p v0:= (h.represents N p N le_rfl).good.labels.boundK
    have hb:= supplement_bound B K' 0 hS hC ht v
    let R:= demo hs; let Q:= Attach.line K' X R q u
    obtain ⟨t,hT,hV⟩:= Extra.Histories.Attach.line_budget K' X R q hb hβ
    have hx:(((Z).plays v).forced) = Q:=rfl -- proof cost unfolds?
    have hv := h.represents N p N le_rfl|>.vac; rw [← hv] at hp
    rw [hx]; refine ⟨t,⟨hT.1,hT.2.1,hT.2.2.trans ?_⟩, hV⟩
    calc _ = Extra.Histories.fee F Y'.p X C v0 *F.coeffSize (F.core v):=by change fullCost _ _ _ * _*_ = fullCost _ _ _*_ * _; rw [show K'.p=Y'.p from rfl];ring -- plate def eq maybe
         _ ≤ _:= by rw [← mul_assoc]; exact mul_le_mul hp (Work.G08.size_core ..) (Work.G08.size_nonneg ..) (mul_nonneg (Real.sqrt_nonneg _) hf)

variable {μ:ℝ}{d0 u:ℕ}
-- Pred.P.bare. Already unit exact.G.Write.Forms
lemma premiere (hv: Heard B H N p A N (summit F B H N p K hs q)): Funds (m:=N) μ A d0 u B Y (summit F B H N p K hs q) (fun v=>Extra.Histories.primary (0:Site (H.S.side N p)) v) (Real.sqrt (v0)) c 1:=by
    intro v g
    let O:= (Z|>.plays v); let I:Coefficient F (H.S.side N p) := Extra.Histories.primary 0 v; have hF: F.coeffSize v=g:= rfl
    let D:= Vinca.decrement O I; have hz: D.support= I.support:=rfl; have hD : D.regular=I.regular:=by change (0: ℕ→ Config G (H.S.side N p)→ℂ)-0=0; rw [sub_zero]
    have hx : D.forced=O.forced:=by change _-0=_; rw [sub_zero]
    have ht':I.Format 0 A Y:= primary_format _; have he : 0<Real.sqrt (v0):=Real.sqrt_pos.mpr (forcedPos ..)
    have hθ:0 ≤ c*g := mul_nonneg hf (hF ▸ (Work.G08.size_nonneg ..))
    have hG:=hv.earns v|>.1
    have hα : D.Format 0 A Y:= ⟨hD.symm ▸ ht'.smooth, ht'.origin,hD.symm ▸ ht'.identity_null,hD.symm ▸ ht'.projects,hx.symm ▸ hG.forcing,hx.symm ▸ hG.carried,hx.symm ▸ hG.invariant,hx.symm ▸ hG.supported,hx.symm ▸ hG.borel⟩
    let Q:Coefficient F (H.S.side N p):=Extra.Histories.primary 0 0
    have hi : Patrons B μ u d0 (Y).p Q 0:=by apply River.patronC _ rfl rfl; simp [Q,Frame.coeffSize,Extra.Histories.primary]
    have hp0: Tab D 0 Y (Real.sqrt (v0)) 0 (c*g):= ⟨he,le_rfl,hθ,hD.symm ▸ (hi.bill he).regular,(hF ▸ hx.symm ▸ vault B A K hs q h hS hC ht hp hf v)⟩
    rw [one_mul]; refine ⟨River.patronC hF.le rfl rfl,ht',rfl,hα,River.tabWeaken hp0 hθ le_rfl,?_⟩
    change F.coeffSize (v-v) ≤ _; rw [sub_self]; exact hi.principal.trans hθ -- hi.x=0
end YM.LocalLTE.Ticket
