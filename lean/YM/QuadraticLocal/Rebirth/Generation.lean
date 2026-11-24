import YM.QuadraticLocal.Rebirth.Life
/-!
# power offsets. The *same* chart back-power prices from any horizon in this construction
 at least the requested offset. Also quantitative CreditF on each offset price.
 (If also need Cost preparation at momentum degree, buy enough
   before parameter selection; don't infer existence of a smoother period-independent
   real beta ratio.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Rebirth.Chart
open Function Filter Finset Lattice RG Wilson Marker
open Comparison.RG02 Comparison.RG02.Adjacent
open Pressure ConnectedActivityE6 AllOrder AllOrder.Catch
open AllOrder.Wheel AllOrder.Floe Next.Scheduling
open PositionX.Jet AllOrder.Response PositionX.Gauss
open AllOrder.Laplace AllOrder.Laplace.SigmaP
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable (Q : Pace.Coin) (h : Q 0=0) (L : ℕ) (s:ℤ)

/- orbit along the arbitrarily high horizon of this application (pay separately!). -/
set_option quotPrecheck false
local notation "F" => (caliber Q h).direct L
local notation "T" => (caliber Q h).back L
local notation "u" => tariff Q h L s
local notation "p" => (Pace.Coin)
local notation "Φ" j:max => (Pace.ladder (grade (s+(j:ℕ))) Q)
-- explicit Nat binder arity.M.Level leg
lemma cannon (n:ℕ) : (fun x:ℝ=> ((F).rating x)^s) * (delay (u) n ∘ ((F).enter)) =ᶠ[𝓝 0] fun t=> ∑ j∈ range (n+1), t^j*( (u) j * (F).rating t ^ (s+(j:ℤ))) :=by
    filter_upwards [(F).bright] with t ht
    unfold delay; simp only [Pi.mul_apply,Function.comp_apply,smul_eq_mul,UnitCost.enter, mul_sum]; refine Finset.sum_congr rfl fun j hj=>?_ ; rw [mul_pow,zpow_add₀ ht.ne',zpow_natCast]; ring
-- inverse convolution. useful for changing order horizon & proving Ω budgets.
lemma charges (n:ℕ)(m:ℕ)(hn:n ≤ L)(hm:m≤n): (∑ j∈range (m+1), (tariff Q h L s j)*(Pace.ladder (grade (s+(j:ℤ))) Q (m-j)))=just 1 m:= by
    let f (i:ℕ):=(fun t=>(u) i *((F).rating t)^(s+(i:ℤ))); let g(i:ℕ):=(fun t:ℝ=>t^i)* f i; have hx: Act n (∑ j∈range (n+1),g j) (just 1):= (composition Q h L s n).realizes ((cannon Q h L s n).mono fun x h=> h.trans (Finset.sum_apply x (range (n+1)) g).symm)
    have hl (i:ℕ):Act n (f i) ((u) i • Φ i):= ((forward Q h L (s+(i:ℤ))).smul ((u) i)).shrink hn; have ht (i:ℕ):ContDiffAt ℝ ω (g i) 0:=(contDiffAt_id.pow i).mul (hl i).nice; rw [← ( (exact_sum («F»:=g) (range (n+1)) (fun i _=>eo_Act n (ht i))).trans_at hx hm), Finset.sum_apply]; symm; refine Eq.trans ?_ (sum_congr (f:=fun i=> someJ (g i) m) rfl ?_) -- sum smaller
    · refine Eq.symm ( (show (∑ i∈range (m+1),someJ (g i) m)=∑ i∈range (n+1),someJ (g i) m from ?_)); apply Finset.sum_subset (range_mono (by omega)); intro i hi hh; unfold g; rw [jo_shift (hl i).nice, if_neg]; simp only [mem_range] at hh; omega
    intro i hi; unfold g; rw [ jo_shift (hl i).nice,if_pos (mem_range_succ_iff.mp hi), (hl i).writes _ (by omega) ]; rfl
lemma history (j:ℕ)(hj:j+1≤ L): tariff Q h L s (j+1) = - (∑ i∈range (j+1),tariff Q h L s i * Pace.ladder (grade (s+(i:ℤ))) Q (j+1-i)):= by
    have ht:= charges Q h L s (j+1) (j+1) hj le_rfl; rw [sum_range_succ] at ht; rw [Nat.sub_self,Pace.start _ h,mul_one] at ht; exact eq_neg_of_add_eq_zero_right ht
lemma parallel (Q':Pace.Coin)(h':Q' 0=0)(k:ℕ)(m:ℕ)(hs:m≤L)(hp:m≤k)(hh:∀ i ≤ m,Q i=Q' i) : tariff Q h L s m=tariff Q' h' k s m:= by
    induction m using Nat.strong_induction_on with
    | h m ih =>
        cases m with
        | zero=> rw [tariff_zero,tariff_zero]
        | succ m=> rw [history Q h L s m hs,history Q' h' k s m hp]; apply congr_arg; refine sum_congr rfl fun i hi=>?_ ; rw [ih i (mem_range.mp hi) (le_trans (by simp only [mem_range] at hi; omega) hs) (by simp only [mem_range] at hi; omega) (fun j h=>hh j (h.trans (mem_range.mp hi).le))]; rw [ Pace.synch (fun j hj=>hh j hj) _ _ (by omega)] -- #check
variable {ι:Type}
variable (Λ:ι→ℝ)(x:ι→Pace.Coin)(hz:∀ i,x i 0=0) {k:ℕ}
-- inverse polynomial on cone. Explicit m-fold product-degree cost bound not optimal.
lemma restatement (hf:∀ i≤ L,Pace.Cost Λ k (fun j=> x j i))(m:ℕ)(hm:m≤L): Pace.Cost Λ (m*k) (fun i=> tariff (x i) (hz i) L s m):= by
    induction m using Nat.strong_induction_on with
    | h m ih=>
        cases m with
        | zero=> simp_rw [tariff_zero]; exact Pace.Cost.fixed _
        | succ m=> simp_rw [history _ _ L _ m hm]; apply Pace.Cost.neg; refine Pace.Cost.sum fun i hi=>?_ ; have ht:i < m+1:= mem_range.mp hi; apply ( (ih i ht (by omega)).mul (Pace.Cost.transfer (j:=m+1-i) (fun k hk=>hf k (by omega)) _)).up; rw [Nat.mul_comm k,← Nat.add_mul,Nat.add_sub_of_le ht.le] -- lemma name change
end YM.QuadraticLocal.Rebirth.Chart
