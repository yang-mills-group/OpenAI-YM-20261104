import YM.FormalOPE.RG10.Sync.Ledger
/-!
 # Time exponential in the register(s)
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Sync
open Filter Topology MeasureTheory Function
open PertExtension.GaussianScore MultiGauge MultiGauge.Splice MultiGauge.Stack MultiGauge.Papers
open YM.Multi.Vacuum.Gauss
open Route PowerSeries Finset
open scoped Classical ContDiff Topology BigOperators ENNReal
variable {I:Type}[Fintype I] {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]

lemma exp_tracks {A B:Ticket E}{r:ℕ} (h:Through r A B): Through r (Stack.exponential A) (Stack.exponential B):= by
 intro i hi; simp_rw [Stack.exponential,coeff_mk,map_sum,Stack.roll,coeff_C_mul]; exact Finset.sum_congr rfl (fun j _=> congr_arg (_ * ·) (h.pow j i hi))

variable (A: Ticket E)(n:ℕ)
 def plate (e:Permit E): Ticket E:= monomial (n+1) e
lemma startsPlate (v:Permit E): constantCoeff (plate n v)=0:= by rw [← coeff_zero_eq_constantCoeff_apply,plate,coeff_monomial]; simp
lemma pierce (v:Permit E): Through n (plate n v) 0:= fun i hi=> by simp [plate,coeff_monomial,show i≠n+1 by omega] -- unused
lemma born_spill (u:Ticket E)(h:incline u)(v:Permit E): coeff (n+1) (u*plate n v)=v:= by
 rw [coeff_mul, Finset.sum_eq_single (0,n+1)];
 · unfold incline at h; simp [plate,h]; -- simp uses incline?
 · rintro ⟨i,j⟩ hq he; have hp:= Finset.mem_antidiagonal.mp hq; have hj:j≠n+1:= by intro a; subst j; apply he; congr; omega
   simp [plate,coeff_monomial,hj]
 simp
lemma exponent_one_row (u:Permit E): Through (n+1) (Stack.exponential (plate n u)) (1+plate n u):= by
 let x:= plate n u; let v (i:ℕ):= Stack.roll ((i.factorial:ℝ)⁻¹)*(x^i)
 intro i hi; refine (Stack.acting (startsPlate n u) (n+1) i hi).trans ?_; change coeff i (∑ j∈range (n+1+1),v j)= _; rw [map_add,map_sum];
 have he: (Finset.range 2).sum (fun j=> coeff i (v j)) = _:=(show (∑ j∈Finset.range 2,coeff i (v j))= coeff i 1 + coeff i x from by simp [Finset.sum_range_succ,v, roll]) -- parser?
 refine Eq.trans (Finset.sum_subset (M:=Permit E) ?_ ?_).symm he
 · exact Finset.range_mono (by omega)
 intro j hj hk; simp only [Finset.mem_range,not_lt] at hk; have hp:j*(n+1) > i:= by nlinarith
 unfold v; rw [Stack.roll,coeff_C_mul]; unfold x plate; rw [monomial_pow,coeff_monomial]; simp [hp.ne]
 def cycle (A:Ticket E): ℕ → Ticket E
 | 0=> 0
 | n+1 => cycle A n + plate n (coeff (n+1) (A-Stack.exponential (cycle A n)))
 def decant (A:Ticket E): Ticket E:= mk fun i=> coeff i (cycle A i)
lemma stays : Through n (cycle A (n+1)) (cycle A n) := by rw [cycle]; simpa only [add_zero] using Through.add (Through.refl (cycle A n)) (pierce n _) -- infer
lemma receded : Through n (decant A) (cycle A n):= by
 intro i hi; rw [decant,coeff_mk]; induction n,hi using Nat.le_induction with
 | base=> rfl
 | succ n hn ih=> rw [stays A n i hn,ih]
lemma onceBlank (A:Ticket E) : constantCoeff (decant A)=0:= by rw [← coeff_zero_eq_constantCoeff_apply,decant,coeff_mk,cycle,map_zero]
lemma rollout (h: incline A): Through n (Stack.exponential (cycle A n)) A:= by
 induction n with
 | zero=> intro i hi; obtain rfl:i=0:= Nat.eq_zero_of_le_zero hi; rw [coeff_zero_eq_constantCoeff_apply,coeff_zero_eq_constantCoeff_apply,initial,h]
 | succ n ih=>
    intro i hi; by_cases hp:i≤n
    · exact (exp_tracks (stays A n) i hp).trans (ih i hp)
    obtain rfl:i=n+1:=by omega
    rw [cycle,OpenSlots.compose_two ..];
    -- inspect rw
    · rw [Through.mul (Through.refl _) (exponent_one_row n _) (n+1) le_rfl, mul_add,mul_one,map_add,born_spill n (exponential (cycle A n)) (initial _) _,map_sub]; abel
    · rw [← coeff_zero_eq_constantCoeff_apply, ←receded A n 0 (Nat.zero_le _), coeff_zero_eq_constantCoeff_apply,onceBlank]
    exact startsPlate ..
theorem soluble {A:Ticket E}(h: incline A): Stack.exponential (decant A)=A:= PowerSeries.ext fun i=> (exp_tracks (receded A i) i le_rfl).trans (rollout A i h i le_rfl)
lemma authority (L:Layout I E)(A:Ticket E): digital L (Stack.exponential A)=advance (digital L A):= by
 apply PowerSeries.ext; intro i
 rw [Route.advance,digital,PowerSeries.coeff_map,Stack.exponential,coeff_mk,coeff_mk]
 simp_rw [map_sum, ← _root_.map_pow, Stack.roll,coeff_C_mul,_root_.map_mul (ink L), PowerSeries.coeff_map, currency, Complex.ofReal_inv, Complex.ofReal_natCast]
 exact Finset.sum_congr rfl fun j _=> by rw [MvPolynomial.C_mul']
end YM.FormalOPE.RG10.Sync
