import YM.Frontier6.Bouquet.Truth.Deposit

/-! Regulator-dependent contact jets. The all-arities convergence proof can
 pass exactly these even in disjoint groups, via `Payroll`. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(T:Veins)(d: Slot→ℕ)(v:(i:Slot)→ S.Field (d i))(s:ℝ)
def seedT : Teller S:=fun p=> { Code:= Unit, payment:=fun _=>⟨d p.here, v p.here⟩, course:=fun _=>0,sits:=by simp }

def prepared : Teller S:= fun p=> WellFounded.fix (measure Pod.card|>.wf) (fun p rec=> if p.card=1 then seedT d v p else partNumber K (fun q=>if h:q.card<p.card then rec q h else seedT d v q) T d p s) p
lemma preparation_eq (p:Pod): prepared K T d v s p= if p.card=1 then seedT d v p else partNumber K (prepared K T d v s) T d p s:=by
    nth_rw 1 [prepared]; rw [WellFounded.fix_eq]; split; rfl; next=>
        apply bills_only K T p; intro i hi; rw [dif_pos (Pod.lt_card hi)]; rfl
lemma oldest (p:Pod)(he:p.card=1): prepared K T d v s p= seedT d v p:=by rw [preparation_eq, if_pos he]
lemma continuation (p:Pod)(hv:1<p.card) (hs:0<s)(he:∀ w:p.Horizon d, Frontier6.Safe K w (2*(2*s))) : Payroll p K d s (prepared K T d v s) T:= by
    exact fun x H f i=> coreAudits K (prepared K T d v s) T d p s (by rw [preparation_eq K T d v s p, if_neg (ne_of_gt hv)]) hs he x H f i
-- genuine jet and power numbers. Coeff orientation chosen by delta: sign from moving tests retained.
variable {p:Pod}
lemma horoscope (u:p.Horizon d): dim (normal p)+(u:ℕ) + p.track d u= p.arityD d:=by
   have he:= u.isLt; unfold Pod.horizon tiers at he; unfold Pod.track kilo dim; omega -- defs
lemma announces {p:Pod}(hv:1<p.card)(w:(prepared K T d v s p).Code) :
    let A:= prepared K T d v s p
    dim (normal p)+ (A.payment w).fst + (A.course w).card ≤ p.arityD d:=by
    let B:= partNumber K (prepared K T d v s) T d p s; have hu:prepared K T d v s p=B:= by rw [preparation_eq K T d v s p, if_neg (ne_of_gt hv)]
    intro A; rw [reaxis_course hu w,reaxis_payment hu w]; let v:= reaxis hu w; have h':v.snd.fst.val ≤ p.track d v.1:= Nat.lt_add_one_iff.mp v.snd.fst.isLt; rw [← horoscope d v.1]; change _+(v.1:ℕ)+v.snd.snd.phrase.card ≤ _; rw [Kin.phrase_size (v.snd.snd)]; exact add_le_add le_rfl h'
end YM.Frontier6.Bouquet
