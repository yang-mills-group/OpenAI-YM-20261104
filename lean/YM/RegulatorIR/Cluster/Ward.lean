import YM.RegulatorIR.Cluster.Cross
import YM.RegulatorIR.Gradient.Polynomial

/-! Product respects action of a homogeneous connection variation on full
packets. Includes no nonlinear invariant premise. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open Function Budget Budget.Packet Budget.Tuple Diagram Gradient Train PowerSeries Finset
open scoped Topology BigOperators Classical ENNReal NNReal PowerSeries
variable {X Y Z : Type}{a b e:ℕ} {T U:Orders X}

def Ranks (a:ℕ)(T:Orders X): Prop:=∀ i,Within (i+a) (T i)
lemma rank_pair (h:Ranks a T)(hh:Ranks b U): Ranks (a+b) (accord T U):=accord_rank h hh
lemma shot_rank (h:Ranks a T)(Γ:Curve X Y): Ranks a (shot Γ T):=by
 intro e r hr
 obtain ⟨i,hi,he⟩:= Finset.exists_ne_zero_of_sum_ne_zero hr
 obtain ⟨j,_,hp⟩:= Finset.exists_ne_zero_of_sum_ne_zero he
 have ht:= h i.1 j (fun hg=> hp (Gradient.insufficient Γ T i.1 j r hg))
 unfold Gradient.drawn at hp; split at hp
 next hd=> have := mem_antidiagonal.mp hi; omega
 contradiction

variable [Fintype X][Fintype Y]
def printed (a:ℕ)(T:Orders X): (Jet X)⟦X⟧:=PowerSeries.mk fun i=> packed (T i) (i+a)
lemma printed_equal (h:Ranks a T)(hh:Ranks a U) (ht:gradedSymmetric T)(hu:gradedSymmetric U) (he: printed a T=printed a U): T=U:=by
 ext1 e;ext1 r; by_cases hv:r∈ range (e+a+1)
 · apply identified _ _ (ht e r) (hu e r); have hx:= congr_arg (coeff e) he; rw [printed,printed,coeff_mk,coeff_mk] at hx; rw [← isolate _ hv,← isolate _ hv]; exact congr_arg _ hx
 rw [show T e r=0 from by by_contra! h'; exact hv (mem_range.mpr (Nat.lt_succ_of_le (h _ _ h'))),show U e r=0 from by by_contra! hh'; exact hv (mem_range.mpr (Nat.lt_succ_of_le (hh _ _ hh')))]
lemma print_mul (h:Ranks a T)(hh:Ranks b U): printed (a+b) (accord T U)=printed a T * printed b U:=by
 ext1 e; rw [coeff_mul, printed,coeff_mk,accord_order,pack_sum]; apply Finset.sum_congr rfl;intro p hp
 rw [printed,printed,coeff_mk,coeff_mk,← crisp_packed _ _ (h p.1) (hh p.2)]
 congr 1; have := mem_antidiagonal.mp hp;omega
lemma printedShot (h:Ranks a T)(Γ:Curve X Y)(e:ℕ): coeff e (printed a (shot Γ T))=ink Γ T (fun v=>v+a) e:=by
 let f:= ink Γ T (fun v=>v+a) e
 rw [printed,coeff_mk,packed]; change (∑ i∈range _,render (shot Γ T e i))=f
 have hx (r): render (shot Γ T e r)= MvPolynomial.homogeneousComponent r f:= snapshot Γ T (fun v=>v+a) e r (fun _ _=>h _)
 have ht (r) (hv:e+a<r): MvPolynomial.homogeneousComponent r f=0:=by rw [← hx,show shot Γ T e r=0 from by by_contra! hp;exact not_lt.mpr (shot_rank h Γ _ _ hp) hv,render_zero]
 simp_rw [hx];nth_rw 2 [← MvPolynomial.sum_homogeneousComponent f]
 rcases le_total (e+a) f.totalDegree with hh|hh
 · apply sum_subset (range_mono (by omega)); intro r _ he; rw [mem_range] at he; exact ht _ (by omega)
 symm; apply sum_subset (range_mono (by omega)); intro r _ he; rw [mem_range] at he; exact MvPolynomial.homogeneousComponent_eq_zero r f (by omega)

section screenS
variable {R A:Type*} [CommRing R] [CommRing A]
-- tilt coefficients and *also* identify tilt variable with original coupling
-- use finite cutoff to avoid the power series algebra whose variables collide.
def sieve (τ:R→+*A⟦X⟧)(P:R⟦X⟧)(e:ℕ): A⟦X⟧:= ∑ i∈range (e+1), τ (coeff i P)*PowerSeries.X^i
lemma sieve_cost (τ:R→+*A⟦X⟧)(P:R⟦X⟧){e i:ℕ}(he:i≤e) : coeff i (sieve τ P e)=∑ p∈antidiagonal i,coeff p.2 (τ (coeff p.1 P)):=by
 rw [sieve,map_sum,Nat.sum_antidiagonal_eq_sum_range_succ (fun p q=>coeff q (τ (coeff p P)))]
 have h k (hk:k∈range (i+1)) : coeff i (τ (coeff k P)* PowerSeries.X^k)=coeff (i-k) (τ (coeff k P)):=by rw [coeff_mul_X_pow',if_pos (show k ≤ i by rw [mem_range] at hk; omega)]
 symm; apply Eq.trans (Finset.sum_congr rfl fun k hk=> (h k hk).symm)
 apply sum_subset (range_mono (by omega));intro x _ hx;rw [mem_range] at hx; rw [coeff_mul_X_pow',if_neg (show ¬ x ≤ i by omega)]
lemma sieve_product (τ:R→+*A⟦X⟧)(P Q:R⟦X⟧)(e:ℕ): coeff e (sieve τ (P*Q) e)= coeff e (sieve τ P e*sieve τ Q e):=by
 let S:=range (e+1); let f (z:ℕ×ℕ):= (τ (coeff z.1 P)*τ (coeff z.2 Q))* PowerSeries.X^(z.1+z.2)
 have hh : sieve τ (P*Q) e= ∑ i∈ S.biUnion (fun i=>antidiagonal i),f i:=by
    rw [Finset.sum_biUnion]; apply sum_congr rfl; intro i _; rw [coeff_mul]; simp_rw [map_sum,map_mul,sum_mul]; exact sum_congr rfl fun p hp=> by unfold f; rw [mem_antidiagonal.mp hp]
    intro i _ j _ hx; exact Finset.disjoint_left.mpr (fun k hi hj=>hx ((mem_antidiagonal.mp hi).symm.trans (mem_antidiagonal.mp hj)))
 have h : sieve τ P e * sieve τ Q e=∑ z∈S ×ˢ S,f z:=by
    unfold sieve; rw [Finset.sum_mul,sum_product]; apply sum_congr rfl; intro i _; rw [mul_sum]; exact sum_congr rfl fun v _=> by unfold f; rw [pow_add,mul_mul_mul_comm]
 rw [hh,h,map_sum,map_sum]; apply sum_subset
 · intro z hz; obtain ⟨i,hi,he⟩:= mem_biUnion.mp hz; refine mem_product.mpr ⟨mem_range.mpr ?_,mem_range.mpr ?_⟩ <;> have hi:= mem_range.mp hi <;> have hv:= mem_antidiagonal.mp he <;> omega
 intro i _ he; unfold f; rw [coeff_mul_X_pow',if_neg]; exact fun hv=> he (mem_biUnion.mpr ⟨i.1+i.2, mem_range.mpr (by omega), mem_antidiagonal.mpr rfl⟩)
end screenS
lemma shot_print (h:Ranks a T)(hh:Ranks b U)(Γ:Curve X Y): printed (a+b) (shot Γ (accord T U))= printed a (shot Γ T)*printed b (shot Γ U):=by
 let τ:= (alter Γ).toRingHom
 have ht {a:ℕ}{T:Orders X}{e i:ℕ} (h:Ranks a T)(he:i≤e) : coeff i (printed a (shot Γ T))=coeff i (sieve τ (printed a T) e):= by rw [sieve_cost τ _ he,printedShot h];simp_rw [printed,coeff_mk]; rfl
 ext1 e; rw [ht (rank_pair h hh) (le_refl e),print_mul h hh,sieve_product,coeff_mul,coeff_mul]
 apply Finset.sum_congr rfl; intro p hp;have hv:= mem_antidiagonal.mp hp; rw [ht (i:=p.1) h (show p.1 ≤ e by omega),ht (i:=p.2) hh (show p.2 ≤ e by omega)]
lemma shot_finite (h:Ranks a T)(hh:Ranks b U)(Γ:Curve X Y): shot Γ (accord T U)=accord (shot Γ T) (shot Γ U) := printed_equal (shot_rank (rank_pair h hh) Γ) (rank_pair (shot_rank h Γ) (shot_rank hh Γ)) (shiftSym Γ _) (accord_sym _ _) ((shot_print h hh Γ).trans (print_mul (shot_rank h Γ) (shot_rank hh Γ)).symm)
end YM.RegulatorIR.Cluster
