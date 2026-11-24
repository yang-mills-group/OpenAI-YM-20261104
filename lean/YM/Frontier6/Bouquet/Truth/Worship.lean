import YM.Frontier6.Bouquet.Truth.Celebrate

/-! Translation of readouts for stage definition and movement of finite
 contact moments. Holds inside fixed detecting clearances. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(A:Teller S)(T:Veins){P Q:Ensemble}(w:ℕ)(p:Pod)
set_option quotPrecheck false
local notation "Ψ"=> me p
-- linear transfer to a probing question opening up only through the chosen channel
variable {Y:Type}[NormedAddCommGroup Y] [NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]
    (x:Seats (only p))(H:Patron S (only p) Y)
def perform (w:ℕ) : S.Field w→L[ℂ] Y:= LinearMap.toContinuousLinearMap (H.toLinearMap (fun _=>0) (Ψ) ∘ₗ Tale.suit K (x (Ψ)) w)
lemma audition (f:S.Field w): perform K p x H w f= H.toLinearMap (fun _=>0) (Ψ) (suit K (x (Ψ)) w f):=rfl
lemma tiesone (g:Program S (only p))(v:Spelling S) : H.toLinearMap g (Ψ) v=H.toLinearMap (fun _=>0) (Ψ) v:=by
    change H (Function.update _ _ _)=H (Function.update _ _ _); apply congr_arg H; ext1 i; rw [Subsingleton.elim i (Ψ),update_self,update_self]
lemma key_bump : (key K H (Ψ) x w)= (perform K p x H w).toLinearMap.compMultilinearMap (hearing p (StageWeight K (x (Ψ)) w)):=by
   ext1 v; unfold key; rw [ticket,tiesone, LinearMap.compMultilinearMap_apply, hearing_at]; rfl -- rw args?

def Expenses (p:Pod)(w:ℕ): Full (fiber (only p)) → S.Field w:= pollen K A T (me p) 0 (hearing p (StageWeight K 0 w))
section
variable {r:ℝ} (f:Full (fiber (only p))) (hr:Fits r f) (hh:0<r)(hg:Frontier6.Safe K w (2*r))
include hr hh hg
lemma price_key : pollen K A T (Ψ) x (key K H (Ψ) x w) f= perform K p x H w (Expenses K A T p w f):=by
   unfold Expenses pollen; rw [key_bump, select_map _ _ _ _ _ _ _ _ (Welcomes.appointed K A T _ _ _ (moment_welcomes K w p x f hr hh hg))]; apply congr_arg (perform ..); unfold select branch essay;
   refine Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl (fun j _=>?_)); simp_rw [ink_at_site K A T w x f hr (hg.down K le_rfl (show r ≤ 2*r by linarith)) j]; -- may rw self loops
end
section Totals
variable (x: Seats P) (H:Patron S P Y) (u: Finset (Down P))
lemma Appointed.rootSum {I:Type*}(s:Finset I){f:I→Full (fiber P)}(h:∀ i∈s, Appointed K A T x H (f i)): Appointed K A T x H (∑ i∈s,f i):=by
   induction s using Finset.induction_on with
   | empty=>simp only [Finset.sum_empty]; exact appointed_zero K A T _ _
   | @insert i s he ih=> rw [Finset.sum_insert he]; exact (h _ (mem_insert_self ..)).plus (ih (fun i hi=> h _ (mem_insert_of_mem hi)))
lemma selects {I:Type*}(s:Finset I) {f:I→Full (fiber P)}(h:∀ i∈s, Appointed K A T x H (f i)): select K A T u x H (∑ i∈s,f i)=∑ i∈s, select K A T u x H (f i):=by
   induction s using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact select_zero ..
   | @insert i s he ih=>have ht:= fun y (hy:y∈s)=>h y (mem_insert_of_mem hy); rw [Finset.sum_insert he, Finset.sum_insert he, select_plus K A T _ _ _ _ _ (h _ (mem_insert_self ..)) (Appointed.rootSum K A T x H s ht),ih ht]
end Totals
variable (d:Slot→ℕ)(w:p.Horizon d)(s:ℝ)
end YM.Frontier6.Bouquet
