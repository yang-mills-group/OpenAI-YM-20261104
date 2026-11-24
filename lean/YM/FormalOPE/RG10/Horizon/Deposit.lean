import YM.FormalOPE.RG10.Horizon.Edition
import YM.FormalOPE.RG10.Horizon.Fiscal
/-! # Exported multilinear report in all-order position normalization

Input and output modules fixed, real basis from Deck. No nonlinear ad-hoc Gram dual to
actual probe read. Field series arguments are formal lists of weights already in $check G$;
at the continuum-test boundary geometry/labels from the justified displays only. Each positive
formal order estimate depends on approximate calibration precision/age. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Clearing
open Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD Panel Panel.Consumer InversionTop
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle Arrangements Apertures Transit Route Capture Weave Film
open scoped Topology BigOperators ContDiff Classical
open PowerSeries Ledger Rates
variable {G:Gauge}{F:Frames G}{R:Rails F}{P:Plan F}{Y:Drivers}{Z:Patience P Y}{r m d h n:ℕ}
variable (M:Apertures.Halo)(E:Fore m)(x:Fin m→ Seats F d) (T:Tuned R Z)
local notation "V" => profit R Z M
local notation "Ω" => Fin m→ Deck F d
local notation "ι" => Deck F h
local notation "w'" => winter R Z M
variable (R Z)
/-- Explicit definition order-by-order multilinear; no convergence choices except those in
Wilson independent prescription. Don't charge actual exports before validating the governing
laws and normalization stencils! -/
def publication (d h:ℕ) : MultilinearMap fps (fun _:Fin m=> Seats F d) (Seats F h) := MultilinearMap.pi (fun i:Deck F h=> program (fun u:Fin m→Deck F d=> V (seat ∘ u) E h i))
lemma speaking (i:Deck F h) : publication R Z M E d h x i= valuation (fun u:Fin m→Deck F d=>V (seat ∘ u) E h i) x:= program_eq ..
lemma storing (v:Ω) (h:ℕ) : publication R Z M E d h (seat ∘ v) = V (seat ∘ v) E h := by
 ext1 i; rw [speaking,valuation,sum_eq_single_of_mem v (mem_univ _)];
 · simp [seat]
 intro y _ hy; obtain ⟨i,hp⟩: ∃ i,y i≠v i:= by contrapose! hy; exact funext hy
 rw [prod_eq_zero (mem_univ i) (by simp [seat,hp]),mul_zero]

lemma compatible {x y:Fin m→ Seats F d} (hx:∀ i j, Through r (x i j) (y i j)) (i:Deck F h): Through r (publication R Z M E d h x i) (publication R Z M E d h y i):= by rw [speaking,speaking]; exact Through.sums fun j _=> (Through.refl _).mul (Through.prods fun a _=> hx a (j a))

variable {R Z}
/-- finite publication precisions must make sense with stencil gates. -/
def Fitted (E:Fore m) (s e:ℕ) : Prop:= ∀ (x:Fin m→Deck F s),Clears r (w' (seat ∘ x) E e) (V (seat ∘ x) E e)

variable (he:Fitted (R:=R) (Z:=Z) (r:=r) M E d h)
include he
local notation "L" => publication R Z M E d h

lemma earned : Clears r (w' x E h) (L x):= by
 intro i n hn; simp_rw [forwards R Z x M E] -- inspect
 rw [speaking]
 exact Assessed.sums (u:=fun (i':Ω) t=> w' (seat ∘ i') E h t i *∏ j,x j (i' j)) univ (fun i' _=> Assessed.times_const (he i' i) _) n hn

lemma tells (i:Deck F h): Through r (L x i) (V x E h i):= fun n hn=> Eq.symm (by rw [corner]; exact (earned M E x he i n hn).limUnder_eq)

-- pay with *actual* convention compressed Fore, new origin no change in gaps. scales near.
lemma certified : Clears r (w' x E h) (V x E h) := by intro i n hn; rw [← tells M E x he i n hn]; exact earned M E x he i n hn
include T
local notation "τ" s:max => (trail R (-s) ∘ x)
lemma striped (hM:Valid F h M)(s:ℝ) : Clears r (w' x (compress s E) h) (V x (compress s E) h):= by
 let U:=τ s; have hx: trail R s ∘ U=x:= funext (fun i=>unfold_trail ..)
 have hv := assessing T M U E hM s (certified M E U he)
 rw [hx] at hv; intro i n hn; rw [corner, (hv i n hn).limUnder_eq]; exact hv i n hn

lemma suits (hM:Valid F h M)(s:ℝ): Fitted (R:=R) (Z:=Z) (r:=r) M (compress s E) d h:= fun x=>striped M E (seat ∘ x) T he hM s

theorem Wilson (hM:Valid F h M)(s:ℝ) (i:Deck F h) : Through r
    (publication R Z M (compress s E) d h x i) (trail R s (L (τ s)) i) := by
 have he' := suits M E T he hM s; let K:=τ s; have hα: trail R s ∘ K=x := funext (fun i=> unfold_trail ..)
 apply Through.trans (tells M (compress s E) x he' i); refine Through.trans ?_ (Through.travel (fun i=> (tells M E K he i).symm) s i);
 have hh (n) (hn:n≤r) := pays_scaled T M K E hM s (certified M E K he) i n hn; rw [hα] at hh; exact hh

omit he
lemma provisions (S: Finset (Vantage F)) (A : ∀ u:Fin m→ Deck F d, Attaches R Z (seat ∘ u) E r h S) (hu:∀ i : Deck F h,exhibit M i∈S)(hM:Valid F h M): Fitted (R:=R ) (Z:=Z ) (r:=r) M E d h := fun x i=> account T hM (A x) hu i
-- preserve arbitrary coefficient boundary
lemma editing {k:ℕ} (hM':Valid F h M) (hk:h ≤ k) (M':Halo) (hM: Valid F k M') (S: Finset (Vantage F))(A:∀ u: Ω,Attaches R Z (seat ∘ u) E r k S)
      (he:∀ i:Deck F k,exhibit M' i∈S)(hf:∀ i:Deck F h,exhibit M i∈S) (i:Deck F h) : Through r (L x i) (publication R Z M' E d k x (Deck.climb F hk i)) := by
 rw [speaking,speaking]; unfold valuation; apply Through.sums; intro j _; exact (Through.mul (concord T hM' hk hM (A j) he hf i) (Through.refl (∏ a,x a (j a))))
end YM.FormalOPE.RG10.Clearing
