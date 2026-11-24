import YM.Integration.WilsonIndependentRawPairBudget
import YM.Integration.WilsonIndependentRawWordTransport

/-! The located first moment salary for the actual, joint raw pair report.
Both placements use the common safe center of this finite board. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentRawPairOpening
open Lattice RG Source Labels PertExtension XSpace XSpace.Rose
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Gain RegulatorIR.Prim RegulatorIR.Motion RegulatorIR.Uniform
open RegulatorIR.Taping RegulatorIR.Halo RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open WilsonIndependentRawNamedProduct WilsonIndependentRawWordGeometry
open scoped Classical ENNReal NNReal
variable {G:Gauge}{I:Type}{M:I→ℕ}{n:Page M→Side}{S:Heir n G}
variable (V:Reel S)(x:I → Room)(o z:I → Cover)

def span (i:I) := dist (x i) (slide 1 (o i)) + dist (x i) (slide 1 (z i))

theorem nonneg (w:I) : 0 ≤ span x o z w := add_nonneg dist_nonneg dist_nonneg

include V in
theorem seated (start:∀ w,S.l (Page.opening M w)=1)(w:I)(u r:ℕ)(t:Packet (Foot G) r) :
    markQ (S.coverQ x u (Page.opening M w)) t = markQ (root (x w) u) t := by
  let s:=Page.opening M w
  change markQ ((Premium.rooted (Tariff.native (S.radius s) (S.radius_pos s) u) (x w)).uses
    (S.maps s).pos) t = _
  rw [V.realms]
  let fare (l:ℝ):= markQ ((Premium.rooted
    (Tariff.native (max 1 l) (lt_of_lt_of_le zero_lt_one (le_max_left ..)) u) (x w)).uses
    (localL l)) t
  change fare (S.l s)=_
  rw [show S.l s=1 from start w]
  have base (l:ℝ)(h:0<l)(he:l=1) : Tariff.native l h u=Tariff.native 1 zero_lt_one u := by
    subst l
    rfl
  exact congrArg (fun K:Tariff Room=>markQ ((Premium.rooted K (x w)).uses (localL 1)) t)
    (base _ _ (max_self (1:ℝ)))

variable (R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(a c:Bool)(d e:ℕ)
    (b:(R.family.labels.level d).Index)(b':(R.family.labels.level e).Index)

include V in
theorem original (T:S.Accounts)(L:Meter I)(p u:ℕ)
    (start:∀ w,S.l (Page.opening M w)=1)
    (budget:∀ w, ENNReal.ofReal (1+span x o z w)≤L.val w) :
    WilsonIndependentRawWordTransport.Opening (p:=p) (x:=x) (u:=u) (L:=L)
      (report R W a c d e b b' T o z) (wage:=1) := by
  intro i _ r
  apply Carry.regular
  refine ⟨_,(u+u)+(u+u),WilsonIndependentRawPairBudget.paid R W a c d e b b' u i r,?_⟩
  intro w
  change markQ (S.coverQ x u (Page.opening M w)) (ranks R W a c d e b b' (o w) (z w) i r) ≤ _
  rw [seated V x start w u r]
  apply (WilsonIndependentRawPairBudget.original R W a c d e b b' u i r (o w) (z w) (x w)).trans
  apply mul_le_mul_right
  rw [pow_add]
  unfold WilsonIndependentRawPairBudget.reach displacement Tariff.amount
  simp only [div_one]
  apply mul_le_mul'
  · apply pow_le_pow_left'
    apply (ENNReal.ofReal_le_ofReal (q:=1+span x o z w) _).trans (budget w)
    unfold span
    linarith [show 0≤dist (x w) (slide 1 (z w)) from dist_nonneg]
  · apply pow_le_pow_left'
    apply (ENNReal.ofReal_le_ofReal (q:=1+span x o z w) _).trans (budget w)
    unfold span
    linarith [show 0≤dist (x w) (slide 1 (o w)) from dist_nonneg]

end YM.Integration.WilsonIndependentRawPairOpening
