import YM.RegulatorIR.Gradient.Train
import YM.RegulatorIR.Diagram.Valence

/-! Tensors at a nonlinear all-degree input curve at fixed first variation
order. `correction` excludes precisely the initial linear-substitution
contribution in the indicated output order. In uses here W is invariant as a
*series*, not slotwise closed; this distinction costs derivatives and lower
orders but not a repeated width factor. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Gradient
open Budget Budget.Packet Budget.Layer Budget.Tuple Budget.Tariff Train Uniform Diagram Function
open scoped ENNReal Topology BigOperators Classical
variable {I J : Type} {r s:ℕ}

def cut (Γ:Curve I J) (T:Packet I r) (s:ℕ) (g:Fin r→ℕ): Packet J (r+s) := if h:charge g=s then h ▸ symmetry (series Γ g T) else 0
def updateQ (Γ:Curve I J)(T:Packet I r)(s:ℕ): Packet J (r+s) := ∑ g∈turns r s,cut Γ T s g
lemma entryZero (g:Fin r→ℕ): charge g=0↔g=0:=by
 constructor
 · intro h; ext x; change g x=0;exact Nat.eq_zero_of_le_zero ((Finset.single_le_sum (f:=g) (fun i _=> Nat.zero_le _) (Finset.mem_univ x)).trans_eq h)
 intro h;rw [h,charge];simp
lemma no_scalar_legs (T:Packet I 0)(Γ: Curve I J) {s:ℕ}(hs:0<s): updateQ Γ T s=0:=by
 unfold updateQ; apply Finset.sum_eq_zero; intro i h; have he:charge i=s:= (turns_iff ..).mp h
 have hh: charge i=0:=by unfold charge;simp
 omega

/-- contribution of input order p, rank i. -/
def drawn (Γ:Curve I J)(W:Orders I)(p s i k:ℕ):Packet J k:=if h:i+s=k then h ▸ updateQ Γ (W p i) s else 0

/-- Extract contribution at coupling degree e and rank k. Since the new rank
is ≥ old, summing over old ranks through k suffices here. -/
def shot (Γ:Curve I J)(W:Orders I) (e k : ℕ) : Packet J k:=
   ∑ p∈Finset.antidiagonal e,∑ i∈Finset.range (k+1), drawn Γ W p.1 p.2 i k

def correction (Γ:Curve I J)(W:Orders I) (e k:ℕ): Packet J k:=
   ∑ p∈ (Finset.antidiagonal e).erase (e,0),∑ i∈Finset.range (k+1), drawn Γ W p.1 p.2 i k

lemma comprehensive (Γ:Curve I J)(W:Orders I) (e k:ℕ): shot Γ W e k= correction Γ W e k + updateQ Γ (W e k) 0:=by
 unfold shot correction; rw [← Finset.sum_erase_add _ _ (show (e,0)∈Finset.antidiagonal e from Finset.mem_antidiagonal.mpr (Nat.add_zero e))]; apply congr_arg
 dsimp only; rw [Finset.sum_eq_single k ?_ ?_, drawn,dif_pos (Nat.add_zero k)];
 · intro b h he;rw [drawn,dif_neg (by omega)]
 simp

def Blank (Γ:Curve I J) : Prop:= ∀ i t,0<t→Γ i t=0
lemma blankUpdate (Γ:Curve I J)(h:Blank Γ) (T:Packet I r) (s:ℕ)(hs:0<s): updateQ Γ T s=0:=by
 apply Finset.sum_eq_zero; intro g hg
 have ht : charge g=s:= (turns_iff ..).mp hg
 rw [cut,dif_pos ht]; subst s;change symmetry (series Γ g T)=_; rw [show series Γ g T=0 from ?_,Diagram.sym_zero]
 obtain ⟨v,hv⟩ : ∃ v, 0<g v:= by
   by_contra! hm; have he:= (entryZero g).2 (funext (fun i=>Nat.eq_zero_of_le_zero (hm i))); omega
 have he (x:Car g J) (a) : trips Γ g a x=0:=by apply Finset.prod_eq_zero (Finset.mem_univ v); rw [h (a v) (g v) hv]; rfl
 funext x; simp [series,tracked,he]
lemma blankShot (Γ:Curve I J)(h:Blank Γ)(W:Orders I) (e k : ℕ) : shot Γ W e k= updateQ Γ (W e k) 0 :=by
 rw [comprehensive]; apply Eq.trans (congr_arg (· + updateQ Γ (W e k) 0) ?_) (zero_add _)
 unfold correction; apply Finset.sum_eq_zero; rintro ⟨a,b⟩ hb; obtain ⟨hp,he⟩:= Finset.mem_erase.mp hb; have he:=Finset.mem_antidiagonal.mp he;change a+b=e at he
 have hc:b≠0:=fun hh=> hp (Prod.ext (show a=e by omega) hh)
 apply Finset.sum_eq_zero;intro i hv;unfold drawn;split
 next hL=> subst k; exact blankUpdate Γ h _ _ (by omega)
 rfl

section Uniform
variable {W:Type}{X Y : W→Type}{Λ : Meter W}{Γ:(w:W)→Curve (X w) (Y w)}
variable {Z:Type}{M:W→Tariff Z}{B:∀ w,Premium (M w)}{x:(w:W) → X w→Z}{y:(w:W) → Y w→Z}
  {T:(w:W) → Orders (X w)}{f:W→ℝ≥0∞}{e k:ℕ}

/-- per-input-coordinate polynomial prices - accepts roots anywhere. -/
def SmoothPrice {W Z:Type}{X Y: W→Type}(Λ:Meter W)(M:W→Tariff Z)(x:∀ w,X w→ Z)(y:∀ w,Y w→Z)(Γ:∀ w,Curve (X w) (Y w))(i:ℕ):=
    ∃ f:W→ℝ≥0∞, Poly Λ f ∧ ∀ w (a:X w), markQ ((Premium.rooted (M w) (x w a)).uses (y w)) (Γ w a i)≤f w

lemma segment (h:∀ q≤s,SmoothPrice Λ M x y Γ q)(hf:Claim Λ (fun w=>(B w).uses (x w)) f fun w=> T w e r): Claim Λ (fun w=>(B w).uses (y w)) f fun w=>updateQ (Γ w) (T w e r) s:=by
 apply Claim.sum; intro g hq
 have hr:charge g=s:= (turns_iff ..).mp hq; simp only [cut,dif_pos hr]; subst s
 apply Claim.robust
 choose c hc H using fun i:Fin r=> h (g i) (show _ ≤ charge g from Finset.single_le_sum (fun v _=>Nat.zero_le (g v)) (Finset.mem_univ i))
 have he (s: Finset (Fin r)): Poly Λ (fun w=>∏ i∈s,c i w) := by
    induction s using Finset.induction_on with
    | empty=> simp; exact Poly.oneQ _
    | insert i s hi ih=> simpa only [Finset.prod_insert hi] using! (Poly.mul (hc i) ih)
 apply Carry.mono (Carry.mul_right hf (he Finset.univ))
 intro w; exact Train.char_budget (Γ w) g (B w) _ _ (T w _ _) (fun i=>c i w) (fun i x=>H i w x)
lemma correction_bill (h:∀ q≤e,SmoothPrice Λ M x y Γ q)(ht:∀ i<e,∀ j,0<j→ Claim Λ (fun w=>(B w).uses (x w)) f fun w=> T w i j): Claim Λ (fun w=>(B w).uses (y w)) f fun w=>correction (Γ w) (T w) e k :=by
 apply Claim.sum; rintro ⟨i,j⟩ hp
 obtain ⟨hne,hh⟩:=Finset.mem_erase.mp hp; have he:=Finset.mem_antidiagonal.mp hh;change i+j=e at he
 have hh : j≠0:=fun hj=>hne (Prod.ext (show i=e by omega) hj)
 apply Claim.sum; intro a _; unfold drawn; split_ifs with hm
 · subst k; cases a with
   | zero=>simpa only [no_scalar_legs _ _ (show 0<j by omega)] using (Claim.zeroQ (B:=fun w=>(B w).uses (y w)) (u:=f) (L:=Λ) (r:=(0+j)))
   | succ a=>exact segment (T:=T) (Γ:=Γ) (fun q ha=> h q (le_trans ha (by omega))) (ht i (by omega) _ (by omega))
 exact Claim.zeroQ
end Uniform
end YM.RegulatorIR.Gradient
