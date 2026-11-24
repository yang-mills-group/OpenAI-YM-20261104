import YM.QuadraticLocal.Kiosk
/-!
# Full polynomial passes through the re-expressions with the real coefficient

Counterpart to `ReadZone`: generalization used when a nonvanishing gas sum
isn't available. Do not take any ratios of vacuum evaluations; even the work
for the support budget doesn't require positivity there. `m` is the factor on
EVERY tested polynomial term independent of the test. This module gives the
exact identities including all mask partners after `normalize` call; budgets
at the same time use the existing `First` & `Second` operations charged at
these specific labels/weights (not another envelope).
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Payments Fusion Attached Canopy GridRenewal.Rain
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{p:BudgetPoint}{X:Pipes G n}{d:Tap G n}{x y e a b c f q:ℝ}{B:ℕ}
variable {U W:Activities G n}
variable {V : Type}[DecidableEq V]{R:Census V}{o:V→Site n}{T ι:Type*}{w:V→ℝ}[Fintype V]
def Audit (m:Config G n→ℝ) (H:Hard T p U.forced U.K o R)(F log:T → Config G n→ Poly R) : Prop:=
 ∀ t A, Summable (packet U p (H.hard t) A) ∧ F t A= (Complex.ofReal (m A)) • (Poly.pass (log t A)* ∑' i, packet U p (H.hard t) A i)
variable (m:Config G n→ℝ) (H:Hard T p U.forced U.K o R)(F log:T → Config G n→ Poly R)
namespace Audit
lemma reads (h:Audit (U:=U) m H F log): ReadZone T p U H F log:= fun t A=> ⟨(h t A).1,_,(h t A).2⟩
lemma pivot (hP:U.forced=W.forced)(hV:U.K=W.K) (h:Audit (U:=U) m H F log): Audit (U:=W) m (Kiosk.shape hP hV H) F log:=by
   have hh t A: (packet W p (H.hard t) A)=(packet U p (H.hard t) A):=by funext i; unfold packet; rw [show U.admissible p A i=W.admissible p A i from (by unfold Activities.admissible; rw [hP])]
   intro t U'; simpa only [Kiosk.shape,hh t U'] using h t U'
-- mixing preserving exact multiplier with corresponding Soft charges
abbrev take (G:Gauge)(d:Tap G n)(m:Config G n→ℝ)(U:Config G n):= m U / Real.exp (∑' i,d.logarithm i U)
lemma first (r:ℕ≃X.Pellet) (H:Hard T p X.kernel d.forced o R)(h:Hard.Soft X d p)
    (hK:H.Paid w p.B (a+1) e)(hS:Hard.SoftPrice X d p.B (a+1) b)(hB:Payments.Rates p.B f e b c)
    (hw:∀ i,0<w i)(ha:0≤a)
    (hZ: Audit (U:=X.pours d) m H F log): Audit (U:=fused r p d) (take G d m) (H.transport r h) F log:=by
 intro t U
 obtain ⟨hx,H'⟩:= hZ t U; obtain ⟨hX,HH⟩:= H.carries r h hw ha hK hS hB t U
 let a' := (Real.exp (∑' i,d.logarithm i U):ℂ); have he (y:ℂ) (w:Poly R) : (y/a') • (a' • w)= y • w := by rw [smul_smul,div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))]
 refine ⟨HH.summable,?_⟩
 unfold take; rw [HH.tsum_eq,H', mul_smul_comm,Complex.ofReal_div]; exact (he _ _).symm

-- after marking the analytic part of an output, adjust using full second ledger
variable [Countable ι]
variable (M:Canopy.ShiftRows T ι G p o R)
set_option linter.unusedSectionVars false
local notation "d'"=> Rack.widen X d
lemma second (H:Hard T p X.kernel d.forced o R)(h:Hard.Soft X d p)
    (hK:H.Paid w p.B (a+1) e)(hS:Hard.SoftPrice X d p.B (a+1) b)(hT:M.Budget w p.B (a+1) x)(hB:Payments.Rates p.B f e (b+x) c)
    (hw:∀ i,0<w i)(ha:0≤a)(hZ:Audit (U:=X.pours d) m H F log)
    (log': T → Config G n → Poly R)
    (he: ∀ t U, log t U=log' t U+M.log t U)
    (ho:∀ t U,(log' t U).part R.quiet=0): Audit (U:=fused (folio G n) p d') (take G d' m) (M.poster h H) F log':=by
   intro t U
   obtain ⟨hx,hF⟩:= hZ t U; have hb:= M.posterSum h H hw ha hS hK hT hB t U; let r:ℂ:=↑(Real.exp (∑' i,(d').logarithm i U)); let y:= (∑' i,packet (X.pours d) p (H.hard t) U i); refine ⟨hb.summable,?_⟩
   have hR : r ≠ 0:= Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _); have hQ(t:T)(U): (M.log t U).part R.quiet=0:=by unfold ShiftRows.log; rw [Poly.share (M.earnings hT hw (add_nonneg ha zero_le_one) t U)]; simp_rw [M.skip]; exact tsum_zero
   let v:ℂ:=Complex.ofReal (m U); unfold take;
   rw [hF,hb.tsum_eq, mul_smul_comm, smul_smul,Complex.ofReal_div]; change _= ((v/r)*r) • _; rw [div_mul_cancel₀ _ hR]; apply congr_arg (v • ·); rw [he, ← GridRenewal.Rain.passes _ (by simp only [Poly.part_plus,ho,hQ,zero_add]), ← GridRenewal.Rain.passes _ (ho ..), GridRenewal.Rain.plus]; ring
end Audit
namespace Kiosk
open Audit
namespace First
variable (S: First p U W e f a)
lemma tickets (hw:∀ i,0<w i)(hb:H.Paid w p.B (a+1) e)(ha:0≤a)(hZ:Audit (U:=U) m H F log): Audit (U:=W) (Audit.take G S.tap m) (First.led H S) F log:=by
    let L0:= S.skeleton; let g:= Audit.first m F log S.roll (Kiosk.shape S.oldP S.oldV H) S.softens (turned _ _ H hb) S.softPaid S.funds hw ha (Audit.pivot (U:=U) (W:=L0.pours S.tap) m H F log S.oldP S.oldV hZ); exact Audit.pivot (U:=fused S.roll p S.tap) ( Audit.take G S.tap m ) _ F log S.projection.symm S.keeps.symm g
end First
namespace Second
variable [Countable ι] (M:Canopy.ShiftRows T ι G p o R)
variable (S: Second p U W e f a x)
set_option maxHeartbeats 400000 in
lemma tickets (hw:∀ i,0<w i)(hK:H.Paid w p.B (a+1) e)(ha:0≤a)(hx:M.Budget w p.B (a+1) x)(hZ:Audit (U:=U) m H F log)
     (L:T → Config G n→ Poly R) (h:∀ t O,log t O=L t O+M.log t O)(hp: ∀ t O,(L t O).part R.quiet=0):
     Audit (U:=W) (Audit.take G (Rack.widen S.skeleton S.tap) m) (Second.canopy H M S) F L:=
    Audit.pivot (U:=fused (folio G n) p _) _ _ _ _ S.projection.symm S.keeps.symm (Audit.second m F log M (Kiosk.shape S.oldP S.oldV H) S.softens (turned _ _ H hK) S.softPaid hx S.funds hw ha (Audit.pivot (U:=U) (W:=S.skeleton.pours S.tap) m H _ _ S.oldP S.oldV hZ) L h hp)
end Second
end Kiosk
end YM.QuadraticLocal
