import YM.FormalOPE.RG10.Carryon.Poll
import YM.FormalOPE.RG10.Horizon.Edition

/-!
# finite oracle dependence of X posture, for commuting universal protocols
This section used to lift known alignments on coefficient limits via the exact universal filters,
without assuming that one `q` works for *all tests*. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Carryon
open Gazebo Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle
open scoped Topology BigOperators ContDiff Classical
open PowerSeries Peal
variable {r k:ℕ}
section ordinary
variable {J T :Type*}[Fintype J]{a:T→ℕ}{E:TestSystem J T a} {b c: Mark J a →fps}
def Sync (r) (f g : Mark J a →fps)(i:T) := ∀ p:Fin (a i)→J, Through r (f ⟨i,p⟩) (g ⟨i,p⟩)

omit [Fintype J] in
lemma Sync.marked (F:Finset T)(h: ∀ i∈F, Sync r b c i)(j) : Through r (b (markIn F j)) (c (markIn F j)):=h _ j.1.property _

lemma Sync.send {p:T}(hP:Sync r b c p){K L : FrameAt J fps}(hK:∀ i j, Through r (K i j) (L i j)) : Sync r (PertExtension.Position.insert J a b K) (PertExtension.Position.insert J a c L) p :=
 fun _=> Through.sums fun s _=> (hP s).mul (Through.prods (fun _ _=> hK _ _))
variable (h : ∀ i∈E.tests, Sync r b c i)
include h
lemma probing : (fun v=>constantCoeff (b v)) ∘ markIn E.tests = (fun v=>constantCoeff (c v)) ∘ markIn E.tests := by
 funext j; simpa only [Function.comp_apply, coeff_zero_eq_constantCoeff_apply] using (Sync.marked _ h j 0 (Nat.zero_le _))
lemma response {K L: FrameAt J fps}(hK:∀ i j, Through r (K i j) (L i j)) (hk:k≤r) : E.response b K k= E.response c L k := by
 unfold TestSystem.response; exact congr_arg E.select (funext fun i => Sync.marked _ (fun t ht=> (h t ht).send hK) i k hk)
lemma prepared : E.repair b=E.repair c:= by
 have hh:E.inspect (fun v=>constantCoeff (b v))=E.inspect (fun v=>constantCoeff (c v)):= by unfold TestSystem.inspect; rw [probing h]
 simp_rw [TestSystem.repair]; split_ifs with hv ht ht
 · generalize HH : E.inspect (fun v=> constantCoeff (b v)) = t at hv hh ⊢; -- dep rw issue
   clear HH
   subst t; rfl
 · exact False.elim (ht (hh ▸ hv))
 · exact False.elim (hv (hh.symm ▸ ht))
 rfl
lemma stack {k:ℕ} (hk:k≤r) : E.stack b k= E.stack c k:= by
 induction k with
 | zero=>rfl
 | succ k ih=>
   rw [TestSystem.stack,TestSystem.stack, ih (Nat.le_trans (by omega) hk)]
   funext i j; unfold TestSystem.patch; rw [prepared h,response (K:= TestSystem.stack E c k) (L:= TestSystem.stack E c k) h (fun x y => Through.refl _) hk]
lemma posing (i j) : Through r (E.position b i j) (E.position c i j) := by
 intro l hl; simp only [TestSystem.position,coeff_mk]; rw [stack h hl]
end ordinary
section atPost
variable {G : Gauge} {F : Frames G} {d : ℕ}
variable {D:Stock F}{p q:Mark (Deck F d) PertExtension.Physical.Profile.n→fps}
variable (h : ∀ i∈(D d).tests,Sync r p q i)
include h
lemma rehouse : crib D p = crib D q := by unfold crib TestSystem.leadingAdjust; rw [probing h]
lemma unroll (i j:Deck F d) : Through r (posture D p i j) (posture D q i j):= by unfold posture; rw [rehouse h]; exact posing (E:=crib D q) h i j
lemma posting (v:PertExtension.Physical.Profile) (he:Sync r p q v) : Sync r (post D p) (post D q) v:= he.send (unroll h)
end atPost
namespace Warp
lemma charges {p q:Warp} {a b:fps}(h:Through r a b)(hp:Through r p.x q.x): Through r (p.charge a) (q.charge b):= by
 intro i hi; rw [turning,turning,AlignSeries.subst_finite p.atOrigin,AlignSeries.subst_finite q.atOrigin]; exact sum_congr rfl fun j hj => by rw [h j ((Nat.le_of_lt_succ (mem_range.mp hj)).trans hi),hp.pow j i hi]

/- Avoid recursion through explicit inverseScale internals; cancel composition on
 each side with smooth formal inverse. -/
lemma pretty {p q:Warp} (hq:Through r p.x q.x) (hr : 0 < r) : p.Hot ↔ q.Hot := by unfold Hot; rw [hq 1 hr]
lemma either {p q: Warp}(h:Through r p.x q.x) : Through r p.refund.x q.refund.x:= by
 rcases Nat.eq_zero_or_pos r with hb|hb
 · intro i hi; have hx:i=0:=by omega
   subst i; simp
 have hh:= pretty h hb
 by_cases hp:p.Hot
 · have hl:= cash q (hh.mp hp)
   have hv: Through r (q.refund.step p).x still.x:= hl ▸ (charges h (Through.refl _)) -- rewrite q.refund in hypothesis
   rw [show p.refund.x = still.charge p.refund.x from (still_charge _).symm, show q.refund.x = (q.refund.step p).charge p.refund.x from ?_ ] -- beware second rw
   · exact charges (Through.refl _) hv.symm
   rw [take, show p.charge p.refund.x=(p.step p.refund).x from rfl,deposit p hp,turning]; exact (subst_X (R:=ℝ) (good q.refund.x q.refund.atOrigin)).symm
 have he (p:Warp)(h:¬p.Hot): p.refund.x=PowerSeries.X:= by simp only [inverseScale]; rw [dif_neg (fun hn=> h (isUnit_iff_ne_zero.mp hn))]
 rw [he p hp, he q (mt hh.mpr hp)]; exact Through.refl _
end Warp
end YM.FormalOPE.RG10.Carryon
