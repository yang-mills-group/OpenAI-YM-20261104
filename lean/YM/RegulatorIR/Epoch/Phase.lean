import YM.RegulatorIR.Epoch.Damped

/-! Dual accrual from drift invoices (β, frame feeds). Can place k away
from both ends. UV retains a clipped rate in common coupling. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Epoch
open Function Set Finset Filter YM.RegulatorIR.Ledger Uniform ENNReal
open scoped Topology ENNReal NNReal BigOperators Classical
variable {X:Type}{M:X→ℕ}{k:ℕ}{u v:ℝ}
namespace Marked
variable (S:Marked M)
section tenants
variable (D:Choice M) (F:Page M→ℝ≥0∞)(hb:∀ w,S.peak (D.choose w)=0)

def forward (i:Page M):Prop := D.age i.bindW ≤ i.downW
def backward (i:Page M):Prop:= i.downW ≤ D.age i.bindW
lemma clip_back {P: Page M→ Prop}(h:∀ w,P (D.choose w))(ht:∀ f:Flap M,backward D f.next→P f.next → P f.prev) : ∀ p:Page M, backward D p→ P p:=by
 suffices he:∀ n,∀ p: Page M, backward D p → D.age p.bindW-p.downW=n → P p by exact fun p h=> he _ p h rfl
 intro n; induction n with
 | zero=>
    rintro ⟨w,i,hh⟩ hu hx; have hj:i=D.age w:=by change D.age w-i=0 at hx; exact le_antisymm hu (by omega)
    subst i; exact h w
 | succ n ih=>
    rintro ⟨w,i,hh⟩ hu hx; have he:i<D.age w:=by change D.age w-i=n+1 at hx;omega
    let t:Flap M:= ⟨w,i,he.trans_le (D.young w)⟩; refine ht t he (ih t.next he ?_); change D.age w-(i+1)=n; change D.age w-i=n+1 at hx;omega
lemma clip_fore {P:Page M→Prop} (h:∀ w,P (D.choose w))(ht:∀ f:Flap M,forward D f.prev→P f.prev→P f.next): ∀ p:Page M,forward D p→P p:=by
 apply Page.proves
 · intro w hx; change D.age w≤0 at hx
   have hp:=h w; rw [show D.choose w=Page.opening M w from by change Page.mk w _ _=Page.mk w _ _;congr; omega] at hp -- dependent elimination
   exact hp
 rintro ⟨w,i,hu⟩ h' hp; let f:Flap M:=⟨w,i,hu⟩; by_cases hP: i ≥ D.age w
 · exact ht f hP (h' hP)
 have H:i+1=D.age w:= le_antisymm (by omega) hp
 have hz:f.next=D.choose w:= by unfold Choice.choose Flap.next;dsimp [f]; simp_rw [H]
 change P f.next;rw [hz];exact h w
include hb
lemma expensesB : ∀ i:Page M,backward D i→ Real.log 2 * (↑(D.age i.bindW - i.downW):ℝ) ≤ -S.peak i:= by
 refine clip_back D ?_ ?_
 · intro w;rw [hb];simp [Choice.choose]
 rintro ⟨w,i,h⟩ hv hu
 let f:Flap M:=⟨w,i,h⟩; change Real.log 2*↑(D.age w-i)≤ -S.peak f.prev; change Real.log 2*↑(D.age w-(i+1))≤ -S.peak f.next at hu; change i+1 ≤ D.age w at hv
 rw [S.mark_P] at hu; rw [show D.age w-i=D.age w-(i+1)+1 by omega]; push_cast [Nat.cast_sub hv] at *; linarith [S.incline f]
lemma expensesC : ∀ i:Page M,forward D i→ Real.log 2 * (↑(i.downW-D.age i.bindW):ℝ) ≤ S.peak i := by
 refine clip_fore D ?_ ?_
 · intro w;rw [hb]; simp [Choice.choose]
 rintro ⟨w,i,h⟩ hv hu
 let f:Flap M:=⟨w,i,h⟩; change Real.log 2*↑(i+1-D.age w)≤ S.peak f.next; change Real.log 2*↑(i-D.age w)≤ S.peak f.prev at hu;change D.age w≤ i at hv
 rw [S.mark_P, show i+1-D.age w=i-D.age w+1 from by omega];push_cast [Nat.cast_sub hv] at *; linarith [S.incline f]
lemma debit (i) (h:backward D i):S.peak i≤0:=by linarith [S.expensesB D hb i h,mul_nonneg (Real.log_nonneg (by norm_num : (1:ℝ)≤2)) (Nat.cast_nonneg (D.age i.bindW-i.downW): (0:ℝ)≤ _)]
lemma credit_p (i)(h:forward D i): 0 ≤ S.peak i:= mul_nonneg (Real.log_nonneg (by norm_num)) (Nat.cast_nonneg _) |>.trans (S.expensesC D hb i h)

-- F schedule monotone away from D. incarnate clipped α/λ etc.
structure Balancer (D:Choice M)(F:Page M→ℝ≥0∞):Prop where
 before i : backward D (Flap.next i)→ F i.next≤F i.prev
 after i : forward D (Flap.prev i) → F i.prev≤ F i.next

omit hb
def ruff (D:Choice M) (i:Page M): ℝ≥0∞:= ↑(D.age i.bindW-i.downW)+↑(i.downW-D.age i.bindW)
lemma ruff_b (i:Page M)(h: backward D i) : ruff D i=(↑(D.age i.bindW-i.downW):ℝ≥0∞):=by rw [ruff,Nat.sub_eq_zero_of_le h]; simp
lemma ruff_c (i:Page M)(h: forward D i): ruff D i=(↑(i.downW-D.age i.bindW):ℝ≥0∞):=by rw [ruff,Nat.sub_eq_zero_of_le h]; simp
lemma ruff_size (D:Choice M) (hP:∀ w,S.peak (D.choose w)=0) : Poly S.age_t (ruff D):=by
 refine ((Poly.standard _ (show ENNReal.ofReal ((Real.log 2)⁻¹)≠⊤ from ENNReal.ofReal_ne_top)).mul (Poly.roof _)).mono ?_; intro i
 have he := Real.log_pos (by norm_num : (1:ℝ)<2)
 have h (n:ℕ)(h:Real.log 2*n≤|S.peak i|) : (n:ℝ≥0∞)≤ ENNReal.ofReal ((Real.log 2)⁻¹)* S.age_t.val i:=by
    change _≤ _* ENNReal.ofReal (S.credit i); rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (inv_nonneg.mpr he.le)]
    apply ENNReal.ofReal_le_ofReal; rw [le_inv_mul_iff₀ he];apply h.trans; exact le_add_of_nonneg_left (by linarith [S.cap i.bindW])
 by_cases hk: forward D i
 · rw [ruff_c D i hk];exact h _ ((S.expensesC D hP i hk).trans (le_abs_self _))
 have hm: backward D i:=le_of_lt (lt_of_not_ge hk);rw [ruff_b D i hm];exact h _ ((S.expensesB D hP i hm).trans (neg_le_abs _))
end tenants
end Marked
end YM.RegulatorIR.Epoch
