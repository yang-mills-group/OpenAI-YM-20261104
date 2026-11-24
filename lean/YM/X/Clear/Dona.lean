import YM.X.Clear.Rafter
/-!
Dyadic tail estimate >critical. Multiplicity handled only by radius comparisons; same lower constant in all tori. Used for multiple images as well.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Interval
open Function Filter Set Metric MeasureTheory Lattice PertExtension LatticePT Finset
open scoped Topology ContDiff BigOperators Pointwise Classical
variable {q:ℕ+} {G:Gauge} {R: Side} {j:ℕ} {n:ℕ}
open Pert.Align Asymptotics Real
variable {α:Type*}
private lemma upperland (d:α→ℕ)(s:Finset α): ∃ M:ℕ,∀ x∈s,d x≤M:= ⟨s.sup d,fun _ h=> Finset.le_sup h⟩
-- dyadic split using trigger exponent dimension
lemma tail_count (C:ℝ)(hc:C≥0){A B:ℕ}(ha:A<B)(d:α→ℕ)(s:Finset α)(p: ∀ r:ℕ,0<r→ ((s.filter fun x=>d x≤r).card:ℝ)≤C*r^A) (r:ℕ)(hr:r>0):
  ∑ x∈ s with r ≤ d x, (d x:ℝ)⁻¹^B ≤ ((2:ℝ)^(A+1)*C)*(r:ℝ)⁻¹^(B-A):= by
   let F(x:α):=(d x:ℝ)⁻¹^B; let G(i j:ℕ):Finset α:=s.filter fun x=> i≤d x ∧ d x<j; let D:=B-A; let M:=(2:ℝ)^(A+1)*C
   have he(r:ℕ)(hr:r>0) : ∑ x∈G r (2*r), F x ≤ M/2*(r:ℝ)⁻¹^D:= by
      have hs : (G r (2*r)).card ≤ (s.filter fun x=>d x≤2*r).card:= card_le_card (fun x hx=>mem_filter.mpr (let ⟨v,h⟩:= mem_filter.mp hx; ⟨v,h.2.le⟩))
      calc
       _ ≤ ∑ _x∈ G r (2*r), (r:ℝ)⁻¹^B := by
         refine Finset.sum_le_sum fun _ hx=>?_ ; apply pow_le_pow_left₀ (by positivity) _; exact inv_anti₀ (by exact_mod_cast hr) (by exact_mod_cast (mem_filter.mp hx).2.1) -- placeholder
       _ = ((G r (2*r)).card:ℝ)*(r:ℝ)⁻¹^B:= by rw [Finset.sum_const,nsmul_eq_mul]
       _ ≤ C*((2*r:ℕ):ℝ)^A*(r:ℝ)⁻¹^B:=by gcongr; exact (Nat.cast_le.mpr hs).trans (p (2*r) (by omega))
       _ = _:= by unfold M; rw [show B=A+D by omega,pow_add ((r:ℝ)⁻¹),pow_succ]; push_cast; rw [inv_pow]; field_simp; ring
   have hl(k i:ℕ)(hi:i>0) : ∑ x∈G i (2^k*i),F x≤ M*(i:ℝ)⁻¹^D:= by
      induction k generalizing i with
      | zero=> rw [show G i (2^0*i) = ∅ by ext; simp only [G,pow_zero, one_mul, Finset.mem_filter,Finset.notMem_empty,false_iff,iff_false]; omega, Finset.sum_empty]; unfold M; positivity
      | succ k ih=>
        let u:=2*i
        have hh: u≤ 2^k*u:=le_mul_of_one_le_left (Nat.zero_le _) (Nat.one_le_of_lt (by positivity))
        have hx : G i (2^(k+1)*i) = G i u ∪ G u (2^k*u):= by
            rw [pow_succ, Nat.mul_assoc]; ext x; have hp:i≤u:=by dsimp [u]; omega
            change x∈G i (2^k*u) ↔ _; simp only [G,Finset.mem_union,mem_filter]; by_cases ha:x∈s<;> simp only [ha, true_and,false_and,false_or] <;> (first| rfl|omega) -- not tauto needs omega split
        have hv:Disjoint (G i u) (G u (2^k*u)):= disjoint_left.mpr fun i h j=> not_le_of_gt ((mem_filter.mp h).2.2) ((mem_filter.mp j).2.1)
        have hy: u>0:= by unfold u; omega
        rw [hx, Finset.sum_union hv]; refine (add_le_add (he _ hi) (ih u hy)).trans ?_
        change M/2 * (i:ℝ)⁻¹^D+M*((2*i:ℕ):ℝ)⁻¹^D ≤ _
        have hM:0≤M:=by unfold M; positivity
        push_cast
        have ht : (2:ℝ)⁻¹^D≤1/2:= by simpa using pow_le_pow_of_le_one (a:=(2:ℝ)⁻¹) (by positivity) (by norm_num) (by omega:1≤D)
        rw [mul_inv,mul_pow]; nlinarith [mul_nonneg hM (show 0≤(i:ℝ)⁻¹^D by positivity), mul_le_mul_of_nonneg_right ht (mul_nonneg hM (show 0≤ (i:ℝ)⁻¹^D by positivity))]
   obtain ⟨L,hL⟩:=upperland d s
   rw [show (s.filter (fun x=> r≤d x))= G r (2^(L+1)*r) from ?_]; exact hl (L+1) r hr
   ext x; simp only [G,mem_filter]; constructor
   · intro h; exact ⟨h.1,h.2,(hL x h.1).trans_lt ((show L<2^(L+1) from Nat.lt_of_succ_lt (Nat.lt_two_pow_self (n:=L+1))).trans_le (le_mul_of_one_le_right (by positivity) hr))⟩
   exact fun h=> ⟨h.1,h.2.1⟩

def rim (o:Site R)(k:ℕ):= halo k {o}
lemma rim_spec (o:Site R)(k:ℕ)(i): i∈rim o k↔ separation o i ≤ k:= by simp [rim,halo_spec]
lemma rim_count (o:Site R)(k:ℕ): (rim o k).card≤ (k+k+1)^4:= by simpa [rim] using Corona.halo_size {o} k

def ticketN (o i:Site R):ℕ:= separation o i + 1
def mass (o i:Site R):ℝ:= ticketN o i
lemma mass_eq (o i:Site R): mass o i=1+pdist (o-i):= by unfold mass ticketN separation; push_cast; ring
lemma mass_pos (o i:Site R): mass o i≥1:= by rw [mass_eq]; simp
lemma tail (o:Site R)(h:ℕ){v:ℕ}(hv:0<v)(hh:4<h): ∑ x:Site R with v ≤ ticketN o x, (mass o x)⁻¹^h ≤ ((2:ℝ)^5*3^4)*(v:ℝ)⁻¹^(h-4):= by
   apply tail_count _ (by norm_num) hh _ Finset.univ ?_ v hv; intro r hr; let K:= (Finset.univ : Finset (Site R)).filter fun x=>ticketN o x≤r
   have he : K.card ≤(r+r+1)^4:= (Finset.card_le_card (s:=K) (fun x hx=> (rim_spec o r x).2 (by have h:= (mem_filter.mp hx).2; unfold ticketN at h; omega))).trans (rim_count o r)
   change (K.card:ℝ)≤_; grw [show (K.card:ℝ) ≤ ↑((r+r+1)^4:ℕ) by exact_mod_cast he,←mul_pow]; push_cast; gcongr; change (r:ℝ)+r+1≤ 3*r; linarith [show (r:ℝ) ≥1 by exact_mod_cast hr]
end YM.PositionX.Interval
