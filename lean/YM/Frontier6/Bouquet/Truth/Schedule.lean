import YM.Frontier6.Bouquet.Truth.Worship

/-!
# Exact moments calculated in the punctured channels (still with a UV
 scale for the convergence proof)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(A:Teller S)(T:Veins){P Q:Ensemble}(d:Slot→ℕ)(p:Pod)
variable {Y:Type}[NormedAddCommGroup Y] [NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]
set_option quotPrecheck false
local notation "Ψ"=> fiber (only p)
abbrev Tone (d:Slot→ℕ) (p:Pod) (w:p.Horizon d):= Fin (p.track d w+1)
abbrev Melody (p:Pod)(d:Slot→ℕ):= Σ w:p.Horizon d, Σ j:Tone d p w, Kin (normal p) j.val
variable (s:ℝ)
def partNumber : Issue S p where
    Code:= Melody p d
    payment a:= ⟨a.1,- Expenses K A T p a.1 (a.snd.snd.event s)⟩
    course a:= a.snd.snd.phrase
    sits a _ h:= a.snd.snd.phrase_in _ h
lemma expenses_pay {w:ℕ}(r:ℝ)(hr:0<r)(hR:Frontier6.Safe K w (2*r))(f:Full (fiber (only p)))(hf:Fits r f): Appointed K A T (P:=only p) 0 (hearing p (StageWeight K 0 w)) f:= (moment_welcomes K w p 0 f hf hr hR).appointed K A T 0 _ _
lemma charges_song (s:ℝ)(n:ℕ)(w:p.Horizon d)(f:Full (fiber (only p)))(hs:0<s)(he:Frontier6.Safe K w (2*(2*s))):
   Expenses K A T p w (portion s n f)= ∑ j:Fin (n+1),∑ i:Kin (normal p) j.val, train (normal p) i.phrase f 0 • Expenses K A T p w (i.event s):=by
    let x(j:Fin (n+1))(i: Kin (normal p) (j:ℕ)):= series (normal p) _ i s f; have ht(j:Fin (n+1))(i: Kin (normal p) (j:ℕ)): Appointed K A T (P:=only p) 0 (hearing p (StageWeight K 0 w)) (x j i):= Appointed.scal (expenses_pay K A T p (2*s) (by positivity) he _ (i.event_size hs)) _ -- cast normal ≠ fiber
    have hJ(j:Fin (n+1)): Appointed K A T (P:=only p) 0 (hearing p (StageWeight K 0 w)) (∑ i,x j i):= Appointed.rootSum _ _ _ _ _ Finset.univ (fun i _=> ht j i)
    let V (j:Fin (n+1)):=∑ i,x j i; let A'(f):= Expenses K A T p w f; change A' _=_; rw [show portion s n f=∑ j:Fin (n+1),V j from portion_series _ s f n]
    have hz(t:Fin (n+1)): A' (V t)=∑ i:Kin (normal p) (t:ℕ), train (normal p) i.phrase f 0 • A' (i.event s):=by
       refine Eq.trans (b:=∑ i: Kin (normal p) (t:ℕ), A' (x t i)) (selects _ _ _ _ _ (proper ..) _ (fun i _=>ht t i)) (sum_congr rfl fun i _=>?_); exact select_scal ..
    exact (selects _ _ _ _ _ (proper (only p) p) Finset.univ (fun i _=>hJ i)).trans (sum_congr rfl fun i _=>hz i)
lemma coreAudits (he: A p=partNumber K A T d p s)(hs:0<s)(hr:∀ w:p.Horizon d, Frontier6.Safe K w (2*(2*s))) : Payroll p K d s A T:=by
   intro Y _ _ _ _ _ x H f i; subst_vars -- likely wrong replaces i?
   obtain rfl:i=me p:= Subsingleton.elim ..
   let P:= normal p; let q:= x (me p); let V(w:p.Horizon d):= perform K p x H w
   let L(I:Issue S p):= ∑ a:I.Code, train (normal p) (I.course a) f 0 • H.toLinearMap (fun _=>0) (me p) (Tale.suit K q (I.payment a).1 (I.payment a).2); rw [show marble K A T (me p) x H f = L (A p) from finest ..,he];
   unfold L; -- simp sigma from definition defeq
   change (∑ a: Melody p d, train (normal p) a.snd.snd.phrase f 0 • V a.1 (-Expenses K A T p a.1 (a.snd.snd.event s)))= -(∑ w:p.Horizon d,pollen K A T _ _ (key K H (me p) x w) (atBook _ _ _ _ f)); rw [Fintype.sum_sigma,← Finset.sum_neg_distrib]; refine sum_congr rfl (fun i _=>?_);
   rw [Fintype.sum_sigma,atOnly,price_key K A T i p x H _ (portion_fits hs _ _) (by positivity) (hr i)]; change _ = -(perform K p x H i (Expenses K A T p i (portion s (p.track d i) f))); rw [charges_song K A T d p s (p.track d i) i f hs (hr i)]; unfold V; simp_rw [map_sum,map_neg,map_smul,←Finset.sum_neg_distrib, smul_neg]; -- may cast issues
end YM.Frontier6.Bouquet
