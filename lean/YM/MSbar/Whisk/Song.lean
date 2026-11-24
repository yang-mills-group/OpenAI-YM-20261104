import YM.MSbar.Whisk.Rails
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Whisk
open Function Filter Finset Cacao
open scoped BigOperators Classical
variable {σ ι A:Type} [Fintype σ]
open Lattice MvPolynomial
local notation "P"=> Pot σ
variable {n:Side}{l : σ→ Site n}{W: Finset (Site n)} {Y Z:Finset (Site n)} {x y z:Site n}{ξ : View σ}
variable {m p q d:ℕ} {r a b t u v:ℝ}{f g:Pot σ}{T R: List σ} {k:σ→σ→ℝ}

-- Excess affects named exterior with weak exponentially priced gate.
variable {B w : ℝ}
def Eve (r:ℝ)(x y:Site n):= Real.exp (r * separation x y)
lemma eve_t (ha:0≤B)(x y z: Site n): Eve B x z ≤ Eve B x y*Eve B y z:=by
   unfold Eve; rw [← Real.exp_add]; apply Real.exp_monotone; rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast separation_triangle x y z) ha
lemma trade (a b : ℝ)(i j:Site n)(p:ℕ): liftW a p (separation i j)*Eve b i j=liftW (a+b) p (separation i j):=by unfold liftW Eve; rw [mul_assoc, ← Real.exp_add,add_mul]
lemma tokenW (hx:x∈W)(hy:y∈W)(hp:0≤B): Eve B x y * spread l W a p T ≤ spread l W (a+B) p T :=by
   have hz:= curve (W:=zone l W T) (mem_union_left _ hx) (mem_union_left _ hy)
   unfold Eve spread liftW; rw [mul_left_comm,← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (by positivity); apply Real.exp_monotone; rw [add_mul,add_comm]; exact add_le_add_right (by exact mul_le_mul_of_nonneg_left (by exact_mod_cast hz) hp) _ -- order
lemma tokenL (hx:x∈W)(hy:y∈W)(h:0≤B): Eve B x y* lump l W a p m ξ f ≤lump l W (a+B) p m ξ f:=by unfold lump; rw [←sheen]; apply shiny; intro i hi; unfold rate; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (tokenW hx hy h) (abs_nonneg _)
lemma token_place {z:Site n}(hx:x∈W)(hp:0≤B): Eve B x z*lump l (insert z W) a p m ξ f ≤ lump l (insert z W) (a+B) p m ξ f:= tokenL (Finset.mem_insert_of_mem hx) (mem_insert_self _ _) hp
lemma tokenJ (ha:0≤ a)(hB:0≤ B)(hp:Vault l {z} (a+B) p (m+1) ξ f t)
      (g' : σ → ℝ)(hc: ∀ i:σ, Vault l {l i} a p m ξ (pderiv i g) (g' i))
      (e:∀ i:σ, ∑ j:σ, |k i j| * liftW a p (separation (l i) (l j))*g' j ≤ Eve B z (l i)*u)(hu:0 ≤ u): Vault l {z} a p m ξ (juncture k f g) (2^m*(t*u)):=by
    have ht:=hp.1; let W:Finset (Site n):={z}
    refine ⟨by positivity,fun j hj=>?_⟩
    let s (i)(v:σ):=liftW a p (separation (l i) (l v))
    let L(i:σ)(k:ℕ):= lump l (insert (l i) W) a p k ξ ((pderiv i) f); have h₀(i k): 0≤ L i k:=lump.nonneg ..
    let L' (i:σ)(k:ℕ):=lump l (insert (l i) W) (a+B) p k ξ ((pderiv i) f)
    have hK(k)(he:k≤m): ∑ i:σ,L' i k ≤ t:=by unfold L';rw [← down];exact hp.2 _ (Nat.add_le_add_right he _)
    have hT(i b) (he: b≤m): lump l {l i} a p b ξ ((pderiv i) g) ≤ g' i:= hc i|>.2 _ he
    let R(i i'): P:= k i i' • ((pderiv i) f *(pderiv i') g)
    let q(i i') := Yarn j (fun A:List Bool=> |k i i'| *s i i'*L i (parts true A)*g' i')
    have hx(i i'): lump l W a p j ξ (R i i') ≤ q i i':=by
       have hh := wired l W ξ (Y:=insert (l i) W) (Z:={l i'}) (f:=(pderiv i) f) (g:=(pderiv i') g) (p:=p) (m:=j) ha (Subset.trans (Finset.subset_insert ..) subset_union_left) (mem_insert_self ..) (mem_singleton_self _)
       unfold R q; rw [lump.smul]; refine (mul_le_mul_of_nonneg_left hh (abs_nonneg _)).trans ?_; rw [← mul_assoc,← sheen]; apply shiny; intro i'' h
       let i0:= parts false i''; let v:= parts true i''; change _* (L i v *_)≤_
       have hx:i0 ≤ m:= (part_le ..).trans (h.trans_le hj)
       apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hT i' i0 hx) (h₀ i _)) (mul_nonneg (abs_nonneg _) (wpos ..|>.le))) (le_of_eq _); ring
    have hL(i:σ)(k':ℕ): L i k'* Eve B z (l i) ≤ L' i k':= (mul_comm ..).trans_le (token_place (x:=z) (by exact Finset.mem_singleton_self _) hB)
    have hp(i): ∑ j:σ,q i j ≤Yarn j (fun A:List Bool=> L' i (parts true A)*u):=by
       unfold q; rw [←scarves]; apply shiny; intro A hA; let y:=L i (parts true A); calc
         _ = y * ∑ j:σ,|k i j| *s i j*g' j:=by rw [mul_sum]; apply sum_congr rfl; intro j _; unfold y; ring
         _ ≤ y* (Eve B z (l i)*u):=mul_le_mul_of_nonneg_left (e i) (h₀ _ _)
         _ ≤ _:=by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hL ..) hu
    refine (lump.totals l W ξ _ _).trans ((sum_le_sum (fun i (_:i∈(Finset.univ:Finset σ))=>(lump.totals ..).trans ((sum_le_sum fun v _=> hx i v).trans (hp i)))).trans ?_)
    -- LHS ∑ i∥; inferred defin issue
    rw [←scarves]; refine (shiny (ι:=Bool) j (g:=fun _=>t*u) (fun i hi=> ?_)).trans ?_
    · rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hK _ ((part_le ..).trans (hi.trans_le hj))) hu
    rw [total_books]; rw [Fintype.card_bool]; push_cast; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hj) (mul_nonneg ht hu)
end YM.MSbar.Whisk
namespace YM.MSbar.Whisk
open Function Filter Finset Cacao
open scoped BigOperators Classical
variable {σ ι A:Type} [Fintype σ]
open Lattice MvPolynomial
local notation "P"=> Pot σ
variable {n:Side}{l : σ→ Site n}{W: Finset (Site n)} {Y Z:Finset (Site n)} {x y z:Site n}{ξ : View σ}
variable {m p q d:ℕ} {r a b t u v B :ℝ}{f g:Pot σ}{T R: List σ} {k:σ→σ→ℝ}
-- Drift δ_C. forward mirrored. symmetric automatic.B weight leak. 
structure Dorian (l:σ→Site n)(x:Site n)(a B:ℝ)(p:ℕ)(k:σ→σ→ℝ)(u:ℝ):Prop where
    positive :0≤u
    upper i : ∑ j:σ, |k i j| * liftW a p (separation (l i) (l j))≤ Eve B x (l i)*u
    lower i : ∑ j:σ,|k j i| * liftW a p (separation (l j) (l i))≤ Eve B x (l i)*u

def Vigor (l:σ→Site n)(x:Site n)(a B:ℝ)(p m:ℕ)(ξ:View σ)(f:Pot σ)(b:ℝ): Prop:=0≤b∧∀ i:σ,Vault l {l i} a p m ξ (pderiv i f) (Eve B x (l i)*b)
lemma Vigor.delta {k':ℕ}(h:Vigor l x a B p m ξ f b)(he:k'≤ m)(hg:b≤u):Vigor l x a B p k' ξ f u:=by refine ⟨h.1.trans hg,fun i=>?_⟩; exact Quote.widen (h.2 i) (mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le) he
lemma Tokew.delta {k':ℕ}(h:Tokew l a p m ξ f b)(he:k'≤ m)(hg:b≤u):Tokew l a p k' ξ f u:=by refine ⟨h.1.trans hg,fun i=>?_⟩; exact Quote.widen (h.2 i) hg he
lemma Tokew.soft (h:Tokew l a p m ξ f b)(he:r≤a)(hr:0≤ r): Tokew l r p m ξ f b := ⟨h.1,fun i=> Quote.cooled hr he (h.2 i)⟩
lemma token_turn (ha:0≤a)(hp:0≤B)(h:LoopNet l (a+B) p k t) (e:Vault l {y} (a+B) p (m+1) ξ f b) (u':Vigor l x a B p m ξ g u): Vault l {y} a p m ξ (juncture k f g) (2^m*(b*(Eve B x y*(t*u)))) := by
    refine tokenJ ha hp e (fun j=> Eve B x (l j)*u) u'.2 (fun i=> ?_) (mul_nonneg (Real.exp_pos _|>.le) (mul_nonneg h.hope u'.1))
    let P₀:=Eve B x y* Eve B y (l i); let f j:= |k i j| * liftW (a+B) p (separation (l i) (l j)); have hr :0≤u:= u'.1
    have hf(j:σ): |k i j| *liftW a p (separation (l i) (l j))* (Eve B x (l j)*u)≤ f j*(P₀*u):=by
         have ht:= Real.exp_pos (B*(separation (l i) (l j):ℝ)); have hc:= (eve_t hp x (l i) (l j)).trans (mul_le_mul_of_nonneg_right (eve_t hp x y (l i)) ht.le); refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hr) (mul_nonneg (abs_nonneg _) (wpos ..|>.le))).trans_eq ?_; unfold f P₀; rw [← trade]; ring
    refine (sum_le_sum (fun j _=>hf j)).trans ?_; rw [← Finset.sum_mul]
    exact ((mul_le_mul_of_nonneg_right (h.glow i) (mul_nonneg (mul_nonneg (Real.exp_pos _|>.le) (Real.exp_pos _|>.le)) hr))).trans_eq (by unfold Eve; ring)
lemma stem_in (ha:0≤a)(hp:0≤B)(h:Dorian l x a B p k t) (e:Vault l {y} (a+B) p (m+1) ξ f b) (hz : Tokew l a p m ξ g u) : Vault l {y} a p m ξ (juncture k f g) (2^m*(b*(Eve B x y*(t*u)))):=by
    refine tokenJ ha hp e (fun _=> u) hz.2 (fun i=>?_) (mul_nonneg (Real.exp_pos _|>.le) (mul_nonneg h.positive hz.1)); rw [← sum_mul]; apply ((mul_le_mul_of_nonneg_right ((h.upper i).trans (mul_le_mul_of_nonneg_right (eve_t hp x y (l i)) h.positive)) hz.1)).trans_eq; ring
lemma Dorian.flip (h:Dorian l x a B p k t): Dorian l x a B p (fun i j=> k j i) t:=by
    refine ⟨h.positive,fun i=> ?_,fun i=>?_⟩
    · simp_rw [separation_comm (l i)]; exact h.lower i
    simp_rw [show ∀ j:σ,separation (l j) (l i)=separation (l i) (l j) from fun j=>separation_comm ..]; exact h.upper i
lemma bulk_stem (ha:0≤a)(hp:0≤B)(h:Dorian l x a B p k t) (e₀ : Tokew l (a+B) p (m+1) ξ f b)(hv:Tokew l (a+B) p (m+1) ξ g u): Vigor l x a B p m ξ (juncture k f g) (2*2^m*b*t*u):=by
    have he:a≤ a+B:= le_add_of_nonneg_right hp; refine ⟨?_,fun j=>?_⟩; · have hh:=h.positive; have hY:= hv.1; have hx:=e₀.1; positivity
    rw [replaces,reversal k f ((pderiv j) g)]; exact Quote.widen (Quote.addN (stem_in ha hp h (e₀.2 j) (Tokew.delta (hv.soft he ha) (by omega) le_rfl)) (stem_in ha hp h.flip (hv.2 j) (Tokew.delta (e₀.soft he ha) (by omega) le_rfl))) (le_of_eq (by ring)) le_rfl
lemma mix_f (ha:0≤a)(hp:0≤B)(h:LoopNet l (a+B) p k t) (e₀: Tokew l (a+B) p (m+1) ξ f b)(hv:Vigor l x a B p (m+1) ξ g u): Vigor l x a B p m ξ (juncture k f g) (2*2^m*b*t*u):=by
    have he:a≤ a+B:= le_add_of_nonneg_right hp
    have H:LoopNet l a p k t:=by
         have he:∀ i j: Site n, liftW a p (separation i j)≤liftW (a+B) p (separation i j):= by intro i j; unfold liftW; gcongr
         exact ⟨h.hope,fun i=> (sum_le_sum fun j _=> mul_le_mul_of_nonneg_left (he (l i) (l j)) (abs_nonneg _)).trans (h.glow i),fun i=> (sum_le_sum fun j _=>mul_le_mul_of_nonneg_left (he (l j) (l i)) (abs_nonneg _)).trans (h.forward i)⟩
    refine ⟨?_,fun j=>?_⟩; · have hh:=h.hope; have hY:= hv.1; have hx:= e₀.1; positivity
    rw [replaces,reversal k f ((pderiv j) g)]; exact Quote.widen (Quote.addN (token_turn ha hp h (e₀.2 j) (Vigor.delta hv (by omega) le_rfl)) (jumble ha H.loom (hv.2 j) (Tokew.delta (e₀.soft he ha) (by omega) le_rfl))) (le_of_eq (by ring)) le_rfl
end YM.MSbar.Whisk
