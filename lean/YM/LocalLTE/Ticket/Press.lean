import YM.LocalLTE.River.Pulp
/-!
## A display for per-colour analytic calculations

Uses Exhibitions in the ACTUAL supported currencies after kinetic, normalization and frames.
Evaluator current canonical coordinates; rebase NOT part of a perturbative-series claim, but full
cost. Output BFA.Distribution conservation. Mark aliases and probes on THE SAME Manufacture are
priced without `Many`; exhibitions bind in the representative selected, not by evaluating on the group.

Not asserted for a separate summation in normalized correlation formula without paying iteration costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Ticket
open Function Filter Lattice Wilson RG Source Labels Extra.Histories Bid
open LocalLTE.Vinca LocalLTE.FrameBox AnalyticBridge VerifiedReset Collection Price PhysicalNext.Repeat Blush
open Push Local Planned.GuardedAtom LocalLTE.River YM.MergeProof
open Finset MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n c:Side}{k d:ℕ}{F:Labels.Frame G d} (D:SectionData F) (A:Hol G) (R:Rep G n)(S:Rep G c)
-- Invent architecture.At mos uniform.Operator tariffs genuine post-m quantities.Play stage at pinpoint at purchase.Proved below.
-- dummy
structure Tariff where
    issue :ℝ
    rare:ℝ
    opener:ℝ
    reader:ℝ
    marker:ℝ
    flag:ℝ
    fOpen:0≤opener -- Regular fees: true=O,H=opener; model Mark, inheritance opener
    fRare:0≤rare -- issue error
    fIssue: 0≤ issue
    fReader: 0≤reader -- true.K
    fMarker:0≤ marker
    fFlag:0≤flag
namespace Tariff
variable (C:Tariff)
def advance (u v w:ℝ) := C.opener*u + C.marker*v + C.opener*w
def due (u v w:ℝ):ℝ:= C.reader*u + C.marker*v + C.opener*w
variable {u v w u' v' w' :ℝ}
include C
lemma advance_ge (h:u≤ u')(hp:v≤ v')(he:w≤ w'):C.advance u v w≤ C.advance u' v' w':= add_le_add (add_le_add (mul_le_mul_of_nonneg_left h C.fOpen) (mul_le_mul_of_nonneg_left hp C.fMarker)) (mul_le_mul_of_nonneg_left he C.fOpen)
lemma due_ge (h:u≤ u')(hp:v≤ v')(he:w≤ w'):C.due u v w≤ C.due u' v' w':= add_le_add (add_le_add (mul_le_mul_of_nonneg_left h C.fReader) (mul_le_mul_of_nonneg_left hp C.fMarker)) (mul_le_mul_of_nonneg_left he C.fOpen)
lemma adv0 (h:0≤u)(hp:0≤v)(he:0≤w):0 ≤ C.advance u v w:=by simpa only [advance,mul_zero,add_zero] using C.advance_ge h hp he
lemma due0 (h:0≤u)(hp:0≤v)(he:0≤w):0 ≤ C.due u v w:=by simpa only [due,mul_zero,add_zero] using C.due_ge h hp he
def first (u v w:ℝ):= C.issue+C.advance u v w
def second (u v w:ℝ)(κ:ℝ):= C.rare+C.due u v w+C.flag*(κ*(w+w)) -- allocate K with denominator precise. w true.b budget.U used for E or K inherited.
lemma first0 (h:0≤u)(hp:0≤v)(he:0≤w):0 ≤ C.first u v w:= add_nonneg C.fIssue (C.adv0 h hp he)
lemma second0 {κ:ℝ}(h:0≤u)(hp:0≤v)(he:0≤w)(hκ:0≤κ):0 ≤ C.second u v w κ:= add_nonneg (add_nonneg C.fRare (C.due0 h hp he)) (mul_nonneg C.fFlag (mul_nonneg hκ (add_nonneg he he)))
lemma advSeries {ι:Type*} {f g h:ι→ℝ}(hf: HasSum f u)(hg: HasSum g v)(hh:HasSum h w):HasSum (fun i=>C.advance (f i) (g i) (h i)) (C.advance u v w):= ((hf.mul_left _).add (hg.mul_left _)).add (hh.mul_left _)
lemma dueSeries {ι:Type*} {f g h:ι→ℝ}(hf: HasSum f u)(hg: HasSum g v)(hh:HasSum h w):HasSum (fun i=>C.due (f i) (g i) (h i)) (C.due u v w):= ((hf.mul_left _).add (hg.mul_left _)).add (hh.mul_left _)
end Tariff
-- Actual chosen loom parameter.Operator. g.Step ℝ. downstream. Unit.Row not approximated.
open Extra.Histories.InputColumn
local notation "Xp"=> Config G n→ℂ
structure Pigment (A:Hol G)(F:Labels.Frame G d)(R:Rep G n)(c:Side) where
    main:F.Index→ Coefficient F c
    gain(U:Support n)(f:Config G n→ℂ)(y:ℝ)(_h:RegFit R 0 d A U f)(_he:R.p.supBounds 0 U f y): Coefficient F c
-- Always predict 0 in supplementary flag rows, not zero test masks. Keep structure mounted.
def idle (F:Labels.Frame G d)(Z:ℕ→ Support n): Coefficient F n:= {x:=0,support:=Z,regular:=0,forced:=0}
structure Dues (P: Gateway F A R c)(Q:Pigment A F R c) (κ τ :ℝ)(a b U V:ℕ)(T:Tariff) : Prop where
    primary (i:F.Index):i≠0 → Exhibition D τ V b A S (P.core i) (Q.main i) κ T.issue T.rare
    gain (X:Support n) (f g:Config G n→ℂ)(x y z:ℝ)(hp:RegFit R 0 d A X f)(hc: RegFit R 0 d A X g)(hz:R.p.supBounds 0 X f x)(hk:Canvas D τ U a R.p X g y) (he:R.p.supBounds 0 X (f-g) z): let x':= R.p.mass X x; let y':= R.p.mass X y; let z':= R.p.mass X z
      Exhibition D τ V b A S (P.reader f X x hp hz) (Q.gain X g y hc hk.value) κ (T.advance x' y' z') (T.due x' y' z')
    forced (f:Config G n→ℂ)(j:ℕ)(x z:ℝ)(hX:f≠0)(ht: SlotFit R 0 j f)(he:∀ U,‖f U‖≤x)(hv:∀ U,‖f U‖≤z):let p:= P.flag f j x ht he
      Exhibition D τ V b A S p (idle F p.support) κ 0 (T.flag*R.p.mass (R.activities.forced j).support z)
variable {f:Config G n→ℂ}
end YM.LocalLTE.Ticket
