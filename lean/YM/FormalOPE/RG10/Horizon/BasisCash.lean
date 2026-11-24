import YM.FormalOPE.RG10.Horizon.Flight
import YM.FormalOPE.RG10.Capture.FarPair

/-!
# Ink on skipping bases across height real & pose-orbit budgets
No perturbative convergence over orders or diagonal power test. `coin r` with through r
Taylor moment convention; membership etc in surrounding files. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Clearing
open Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD Panel Panel.Consumer InversionTop
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle Arrangements Apertures Transit
open scoped Topology BigOperators ContDiff Classical
open PowerSeries
variable {G:Gauge}{F:Frames G}{R:Rails F}{P:Plan F}{Y:Drivers}{Z:Patience P Y}
   {X A : Type*} {s t C ξ : ℝ}{r n:ℕ}
abbrev coin (r:ℕ)(a:fps) := Transit.rate r (into a)
def total (r:ℕ)(v:Finset X) (L:X→Series) := ∑ i∈v, rate r (L i)
lemma cstate (u:fps) : coin r u=∑ i∈range (r+1), ‖coeff i u‖ := by simp [coin,rate,into_coeff]
lemma rstate (u:fps) (h:n ≤ r) : ‖coeff n u‖ ≤ coin r u:= by simpa [coin,into_coeff] using (Transit.in_rate (into u) h)
lemma coined (u:fps): 0 ≤ coin r u:= rate_nn ..
lemma coin_neg (u:fps): coin r (-u)=coin r u:=by simp [cstate]
lemma coin_sub_rev (u v:fps): coin r (u-v)=coin r (v-u):=by rw [← neg_sub v u,coin_neg]
lemma coin_add (u v: fps): coin r (u+v) ≤ coin r u+coin r v:=by unfold coin; rw [map_add]; exact rate_add ..
lemma coin_mul (u v: fps): coin r (u*v) ≤ coin r u*coin r v:=by unfold coin; rw [map_mul]; exact rate_mul ..
lemma rate_fore (s:Finset X) (a:X→Series): rate r (∑ i∈s,a i) ≤ ∑ i∈s,rate r (a i) := by induction s using Finset.induction_on with
 | empty=>simp
 | insert i s hi ih=> rw [sum_insert hi,sum_insert hi]; exact (rate_add ..).trans (add_le_add (le_refl _) ih)
lemma coin_fore (s:Finset X)(a:X→fps): coin r (∑ i∈s,a i)≤∑ i∈s,coin r (a i):=by unfold coin; rw [map_sum]; exact rate_fore ..
lemma rate_number (c:ℝ)(h:0≤c) : rate r (PowerSeries.C (c:ℂ)) = c := by
 unfold rate; rw [sum_eq_single_of_mem 0 (mem_range.mpr (by omega))];
 · simp [Real.norm_of_nonneg h]
 intro i hi hx; simp [coeff_C,hx]

def realCase : RG10.Series →+ fps where
  toFun f:= PowerSeries.mk fun i=>(coeff i f).re
  map_zero':= by ext; simp
  map_add' x y:= by ext; simp
lemma real_to (a:Series)(n:ℕ): coeff n (realCase a)=(coeff n a).re:= by simp [realCase]
lemma real_paid (a:Series) : coin r (realCase a) ≤ rate r a:= by
 rw [cstate]; apply Finset.sum_le_sum; intro x hx; rw [real_to]; exact Complex.abs_re_le_norm ..
lemma real_from (a:fps): realCase (into a)=a:= by ext k:1; simp [real_to,into_coeff]
lemma real_mu (a:Series) (b:fps) : realCase (a * into b) = realCase a * b:= by ext k:1; simp only [real_to,coeff_mul,Complex.re_sum,Complex.mul_re,into_coeff,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero];

-- other gauge/period operations not shown, but this one critical *post* engineering convention
lemma echo_linear {U J:ℕ→Type}[∀ i, Fintype (J i)] (V:Voyage U J){k N : ℕ}(h:k ≤ N)(v:Route.Channel (U N))(x: Series):
    Transit.echo V k N (x • v) = x * Transit.echo V k N v:= by
 change Transit.void _ (V.yield k N (x • v))= _ * Transit.void _ _; rw [V.pay h,Algebra.smul_def,map_mul]; congr 1; ext; rw [Transit.first,Route.income_P]; simp

-- scalar ℝ projection of restores. keep rotations eventually. No real spectral statements.
variable {B:Type*}[Fintype B]{ι : Type*}[Fintype ι]
lemma sums_real [DecidableEq B] {L: (B→fps) →ₗ[fps] fps} (v:B→Series):
    realCase (∑ i,v i*into (L (Pi.single i 1)))= L (fun x=> realCase (v x)) := by
 rw [map_sum]; simp_rw [real_mu];
 let f:= ∑ i, (realCase (v i)) • (Pi.single i 1:B→fps); have he:f=(fun x=>realCase (v x)):=by
   ext1 x; unfold f; rw [Finset.sum_apply]; simp [Pi.single_apply,mul_ite]
 rw [← he]; unfold f; rw [map_sum]; simp_rw [map_smul]; rfl
lemma from_full (Q : ι→B→Series)(x:ι→Series)(f:B→fps) :
    ∑ i,x i*(∑ j,Q i j*into (f j))=∑ j,(∑ i,x i*Q i j)*into (f j):=by simp_rw [Finset.mul_sum,Finset.sum_mul,← mul_assoc]; exact Finset.sum_comm
lemma rate_many (Y:ℝ)(x v : ι→ Series)(hu:∀ i,rate r (v i) ≤ Y): rate r (∑ j,x j*v j) ≤ Capture.scaleC r x * Y:= by
  apply (rate_fore ..).trans;
  rw [Capture.scaleC, Finset.sum_mul]; apply Finset.sum_le_sum; intro j _; exact (rate_mul ..).trans (mul_le_mul_of_nonneg_left (hu j) (rate_nn ..))
end YM.FormalOPE.RG10.Clearing
