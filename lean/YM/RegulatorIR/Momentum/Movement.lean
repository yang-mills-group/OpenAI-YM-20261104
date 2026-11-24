import YM.RegulatorIR.Budget.Packet
import YM.Laurent.Eval

/-!
# Multidimensional FD currencies
A variant of MultiNext/SIGNED_SOURCE_CONTINUATION/Newtown Newton proof for
ALL moving legs of a tensor simultaneously, under a quota seminorm (not
assuming a Banach completion in infinite norm). Signed offsets. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Momentum
open Function Set Filter Finset Budget Budget.Packet Budget.Tuple Lattice Laurent
open scoped Topology ENNReal NNReal BigOperators Classical
variable {J X:Type}
abbrev Moves (J:Type) := Laurent.Shift J
-- normally list D= moving slots × axes
variable [DecidableEq J]
def hop (i:J): Moves J:= Pi.single i 1
@[simp] lemma hops (i j:J): hop i j=if j=i then 1 else 0:=by cases eq_or_ne i j <;> rename_i h; subst h;simp [hop]; rw [hop,Pi.single_eq_of_ne h.symm, if_neg h.symm]
section ticks
variable {M:Type} [AddCommGroup M][Module ℝ M]
def spring (U:Moves J→ M)(i:J)(v:Moves J) := U (v+hop i)-U v
def journey (U:Moves J→ M) : List J→ Moves J→ M
| []=>U
| a::l=>journey (spring U a) l
omit [Module ℝ M] in
lemma leapC (U:Moves J→M)(i j:J): spring (spring U i) j=spring (spring U j) i:=by ext1 x; unfold spring; rw [add_right_comm x]; abel
variable [Fintype J]
def portion : ℕ→(Moves J → M)→Moves J → M
| 0,U,_=>U 0
| n+1,U,v=> ((n:ℝ)+1)⁻¹ • ∑ i:J, (v i:ℝ) • portion n (spring U i) (v-hop i)
lemma nearest (U:Moves J→ M)(i:J) (v:Moves J)(n): portion (n+1) U (v+hop i) - portion (n+1) U v=portion n (spring U i) v:=by
 induction n generalizing U i v with
 | zero =>
    simp_rw [portion,Nat.cast_zero, zero_add, inv_one, one_smul, Pi.add_apply,Int.cast_add,add_smul, Finset.sum_add_distrib, add_sub_cancel_left]; simp [ite_smul]
 | succ n ih=>
    have he (j:J): portion (n+1) (spring U j) (v+hop i-hop j)-portion (n+1) (spring U j) (v-hop j)=portion n (spring (spring U i) j) (v-hop j):=by rw [show v+hop i-hop j=v-hop j+hop i from by abel,ih,leapC]
    let f(j:J):=portion (n+1) (spring U j) (v+hop i-hop j);let g (j:J):=portion (n+1) (spring U j) (v-hop j)
    let t:ℝ:=(n:ℝ)+1; have ht:t≠0:=by unfold t; positivity
    change ((↑(n+1)+1:ℝ))⁻¹ • ∑ j:J, (((v+hop i) j:ℤ):ℝ) • f j - ((↑(n+1)+1:ℝ))⁻¹ • ∑ j:J, (v j:ℝ) • g j = _
    rw [← smul_sub]
    simp only [Nat.cast_add,Nat.cast_one, Pi.add_apply, Int.cast_add, add_smul,sum_add_distrib]
    let p:= ∑ j:J, (v j:ℝ) • portion n (spring (spring U i) j) (v-hop j)
    have h : (∑ j:J,(v j:ℝ) • f j)-∑ j:J,(v j:ℝ) • g j=p :=by rw [← sum_sub_distrib]; simp_rw [← smul_sub,f,g,he]; rfl
    rw [show (∑ j:J,(hop i j:ℝ) • f j)= t⁻¹ • p from ?_,add_sub_right_comm,h]
    · change (t+1)⁻¹ • (p+t⁻¹ • p)=t⁻¹ • p; rw [smul_add,smul_smul,← add_smul]; congr 1; unfold t;field_simp
    simp only [hops]; rw [Finset.sum_eq_single i (fun b _ hb=>by simp [hb]) (fun h=>False.elim (h (mem_univ _)))]; simp [f];rfl
lemma into (U:Moves J→ M)(i): portion (i+1) U 0=0:=by simp [portion]
def deposit (U:Moves J→ M)(i) := ∑ n∈Finset.range i, portion n U
def rest (U:Moves J→ M)(i):= U-deposit U i
lemma debt (U:Moves J→ M)(n):rest U (n+1) 0=0:=by simp_rw [rest,Pi.sub_apply,deposit,Finset.sum_apply,sum_range_succ',into]; simp [portion]
lemma move_due (U:Moves J→ M)(i:J)(n): spring (rest U (n+1)) i=rest (spring U i) n := by
 ext1 v; change (U _ - deposit U _ _) - (U _- deposit U _ _)=(spring U i v)-deposit (spring U i) _ v
 rw [show deposit (spring U i) n v=deposit U (n+1) _-deposit U (n+1) v from ?_]
 · unfold spring;abel
 unfold deposit; simp_rw [Finset.sum_apply,sum_range_succ']; rw [show portion 0 U (v+hop i)=portion 0 U v from rfl,add_sub_add_right_eq_sub,← sum_sub_distrib]; simp_rw [nearest]

-- expose falling stencil polynomial as product along a sequenced displacement
abbrev Sequence (J:Type)(n:ℕ):= Fin n→J
def rateP : (n:ℕ)→ Sequence J n → Moves J→ℝ
| 0,_,_=>1
| n+1,s,v=> (v (s 0):ℝ) * rateP n (Fin.tail s) (v-hop (s 0))
def stamps : (n:ℕ)→Sequence J n→List J
| 0,_=>[]
| n+1,s=> s 0 :: stamps n (Fin.tail s)
omit [DecidableEq J] [Fintype J] in
lemma stamps_length (n:ℕ)(u:Sequence J n): (stamps n u).length=n:=by induction n with | zero=>rfl | succ n ih=> rw [stamps,List.length_cons,ih]
lemma particles (U:Moves J→M)(n:ℕ)(v): portion n U v=(Nat.factorial n:ℝ)⁻¹ • ∑ i:Sequence J n, rateP n i v • journey U (stamps n i) 0:=by
 induction n generalizing U v with
 | zero=> simp [portion,rateP,journey,stamps]
 | succ n ih=>
    rw [portion]; simp_rw [ih]; rw [← (Tuple.glueEquiv J n).sum_comp (fun p=>rateP (n+1) p v • _),Fintype.sum_prod_type, Finset.smul_sum,Finset.smul_sum]; apply sum_congr rfl;intro i _
    simp_rw [smul_comm (v i:ℝ) _,smul_sum]; apply sum_congr rfl; intro j _
    rw [show Tuple.glueEquiv J n (i,j)=Fin.cons i j from rfl, rateP, stamps, Fin.cons_zero, Fin.tail_cons]
    simp_rw [journey,smul_smul]; rw [Nat.factorial_succ]; congr 1; push_cast; rw [mul_inv];ring
end ticks
end YM.RegulatorIR.Momentum
