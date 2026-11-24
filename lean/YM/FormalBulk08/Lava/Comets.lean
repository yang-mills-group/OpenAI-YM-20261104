import YM.FormalBulk08.Lava.Dip

/-! Works without trace-norm assumptions at r=0; the constants it computes at
infinite volume are NOT usable, but are never needed at a different rank. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Lava
open Series Wick Orb MvPolynomial
open scoped BigOperators Classical
variable {V : Type*} (q : V→V→ℝ)
abbrev OrbitV (V : Type*) := ℕ→Veil V
def subsetW {n} (p : (k : ℕ)→ k<n → OrbitV V) : Waves V := fun k=> if h:k<n then p k h else 0

def swim (A : OrbitV V) : Waves V := WellFounded.fix Nat.lt_wfRel.wf fun s p=> match s,p with
   | 0,_=> A
   | n+1,p=>fun e r=> ((n+1:ℕ):ℝ)⁻¹ • (stare q (p n (Nat.lt_succ_self n) e (r+1+1))+ brawl q (subsetW p) (subsetW p) n e r)

lemma swim_first (A : OrbitV V) : swim q A 0=A:=WellFounded.fix_eq ..

lemma brawl_match {p t u v : Waves V} (n : ℕ) (e r : ℕ) (h : ∀ i≤n,p i=t i) (l : ∀ i≤n,u i=v i) : brawl q p u n e r=brawl q t v n e r := by
   unfold brawl; refine Finset.sum_congr rfl fun i hi=> Finset.sum_congr rfl fun j hj=> ?_
   rw [Finset.mem_antidiagonal] at hj; rw [h _ (by omega),l _ (by omega)]
lemma swim_succ (A : OrbitV V) (n e r) : swim q A (n+1) e r = ((n+1:ℕ):ℝ)⁻¹ • (stare q (swim q A n e (r+1+1))+ brawl q (swim q A) (swim q A) n e r) := by
   unfold swim; rw [WellFounded.fix_eq]; dsimp only; congr 2; refine brawl_match q n e r ?_ ?_ <;> intro j hj <;> exact dif_pos (Nat.lt_succ_of_le hj)
lemma posting_swim (f : Pap V) [Fintype V] (hp : PowerSeries.coeff 0 f=0) : posting (coal q f)=swim q (fun e r=>marble r (PowerSeries.coeff e f)) := by
   funext n; let p:=posting (coal q f)
   induction n using Nat.strong_induction_on with
   | _ n ih=>
      funext e r
      cases n with
      | zero=>rw [swim_first]; simp_rw [posting,read_initial,coal_initial q f hp]
      | succ n=>
         have he:=stone_curve q f hp n e r; dsimp only at he
         rw [swim_succ, ←ih _ (by omega), ←brawl_match q n e r (fun i hi=> ih i (by omega)) (fun i hi=> ih i (by omega)),←he];rw [inv_smul_smul₀ (by positivity)]
lemma swim_agate (A : OrbitV V) (h : ∀ e r, Agate (A e r)) (n e r) : Agate (swim q A n e r) := by
   induction n generalizing r with
   | zero=> rw [swim_first];apply h
   | succ n ih=> rw [swim_succ]; exact (((ih _).staring q).add (brawl_agate _ _ _ _ _ _)).smul _

-- marks rank bound distinct. useful for future. normalized denominator

def dipper (p : Waves V) (A : OrbitV V) : Waves V := WellFounded.fix Nat.lt_wfRel.wf fun s t=> match s,t with
   | 0,_=>A
   | n+1,u=>fun e r=> ((n+1:ℕ):ℝ)⁻¹ • (stare q (u n (Nat.lt_succ_self n) e (r+1+1)) + (2:ℝ) • brawl q p (subsetW u) n e r)
lemma dipper_first (p : Waves V) (A : OrbitV V) : dipper q p A 0=A:=WellFounded.fix_eq ..
lemma dipper_succ (p : Waves V) (A : OrbitV V) (n e r) : dipper q p A (n+1) e r = ((n+1:ℕ):ℝ)⁻¹ • (stare q (dipper q p A n e (r+1+1))+ (2:ℝ) • brawl q p (dipper q p A) n e r) := by
   unfold dipper; rw [WellFounded.fix_eq]; dsimp only; congr 3; refine brawl_match q n e r (fun _ _=>rfl) ?_; intro j hj; exact dif_pos (Nat.lt_succ_of_le hj)
lemma posting_dipper (f t : Pap V) [Fintype V] (hp : PowerSeries.coeff 0 f=0) (s : ∀ i j,q i j=q j i) :
      posting (flare q f t) = dipper q (posting (coal q f)) (fun e r=>marble r (PowerSeries.coeff e t)) := by
   funext n; induction n using Nat.strong_induction_on with
   | _ n ih=>
     funext e r; cases n with
     | zero=> rw [dipper_first]; simp_rw [posting,read_initial,flare_initial q f t hp]
     | succ n=>
        have he:=stone_mark q f t hp s n e r; dsimp only at he
        rw [dipper_succ,←ih _ (by omega),←brawl_match q n e r (fun i _=>rfl) (fun i hi=>ih i (by omega)),←he, inv_smul_smul₀ (by positivity)]
end YM.FormalBulk08.Lava
