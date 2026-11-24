import YM.FormalBulk08.Lava.Comets

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Lava
open Series Wick Orb MvPolynomial
open scoped BigOperators Classical
variable {V : Type*} (q : V→V→ℝ)
lemma length_void {m n} (h : m=n) : lengthen h (0 : Tile V m)=0 := by cases h; rfl
lemma brawl_vigil {p u : Waves V} (n e r : ℕ) (h : ∀ a∈Finset.antidiagonal e, ∀ b∈Finset.antidiagonal n, ∀ i∈Finset.antidiagonal r, p b.1 a.1 (i.1+1)=0 ∨ u b.2 a.2 (i.2+1)=0) : brawl q p u n e r=0 := by
   unfold brawl reach; refine Finset.sum_eq_zero fun a ha=> Finset.sum_eq_zero fun b hb=> Finset.sum_eq_zero fun i _=> ?_
   rw [visor_eq]; obtain hh|hh:=h a ha b hb i i.property
   · rw [hh,bond_void,sand_nil,length_void]
   rw [hh,bond_wane,sand_nil,length_void]
lemma brawl_rule {p u : Waves V} (R S T : ℕ →ℕ→ℕ →Prop)
   (n e r : ℕ) (h : ¬ T n e r) (A : ∀ a≤n,∀ b c,p a b c ≠ 0 → R a b c)
   (B : ∀ a≤n,∀ b c,u a b c ≠ 0 → S a b c)
   (P : ∀ a b c d i j, a+c=n → b+d=e → i+j=r → R a b (i+1) → S c d (j+1) → T n e r) : brawl q p u n e r=0 := by
   refine brawl_vigil q n e r fun a ha b hb i hi=>?_ ; simp_rw [Finset.mem_antidiagonal] at ha hb hi
   by_contra! hh; exact h (P _ _ _ _ _ _ hb ha hi (A _ (by omega) _ _ hh.1) (B _ (by omega) _ _ hh.2))
lemma swim_rule {p : OrbitV V} (R : ℕ→ℕ→ℕ→Prop) (n e r) (A : ∀ e r, p e r≠0→ R 0 e r)
     (B : ∀ a b c,R a b (c+1+1) → R (a+1) b c)
     (Q : ∀ a b c d i j,R a b (i+1) → R c d (j+1) → R (a+c+1) (b+d) (i+j)) : swim q p n e r ≠ 0 → R n e r := by
   induction n using Nat.strong_induction_on generalizing e r with
   | _ n ih=>
     cases n with
     | zero=> rw [swim_first]; exact A _ _
     | succ n=>
       contrapose!;intro h
       rw [swim_succ]; have he : swim q p n e (r+1+1)=0:= by by_contra hh; exact h (B _ _ _ (ih n (by omega) _ _ hh))
       have hh (a) (ha : a≤n) (b c : ℕ) : swim q p a b c ≠ 0 → R a b c:= ih a (by omega) _ _
       rw [he,stare_nil,brawl_rule q R R (fun a b c=>R (a+1) b c) n e r h hh hh (fun _ _ _ _ _ _ ea eb ec x y=>ea ▸ eb ▸ ec ▸ Q _ _ _ _ _ _ x y),add_zero,smul_zero]
/-- g-positivity, valence, parity -/
def Fiery (A : OrbitV V) := ∀ e r, A e r≠0 → e≥1 ∧ r≤e+2 ∧ r%2=e%2
lemma thermal {p : OrbitV V} (h : Fiery p) (n e r) : swim q p n e r ≠ 0 → e≥1 ∧ r≤e+2 ∧ r%2=e%2 ∧ r+2*n≤3*e :=
   swim_rule q (fun n e r=> e≥1 ∧ r≤e+2 ∧ r%2=e%2 ∧ r+2*n≤3*e) n e r (fun b c hi=>by have := h b c hi; omega) (fun a b c hu=>by  omega) (fun a b c d i j hv hu=>by omega)
end YM.FormalBulk08.Lava
