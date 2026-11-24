import YM.MatchingLedger.Invoice.Cookie

/-!
# Disposing support and unrestricted-angle expenses on the post-L calibration

`acres + q^d` (q log schedule) handled as something growing in number of coarse output
sites, not fine lengths. Include enough spare room for fixed-order external logs q^d. This
benchmark isn't using every available bit of the published schedule. d also bounds solver order
and polynomial mark degree. Larger d biases the prices but forecasts `Blister.solar` agree at
fixed k (not asking finite output OPE equality here).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Kiosk
open Function Filter Lattice RG Wilson Tree Pressure Pressure.Stores Precision Push.Uniform
open PatchArea Action Periodical Books Gazette Set Metric
open MeasureTheory
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff Finset
variable {G : Gauge} {A : ChartRatio G}

section power
variable {d : ℕ} (H : Budget G A (d+3)) (P : Patch) (K : KernelChoices)
local notation "M" => H.income P K

def rangePay (d : ℕ) (q : ℝ):= q ^ (3*d+8)
def refund (d : ℕ)(q : ℝ):= (rangePay d q)^(d+d+3)
lemma price_open (d : ℕ){q : ℝ}(h:1≤q): q^d ≤ rangePay d q := pow_le_pow_right₀ h (by omega)
lemma price_q (d : ℕ){q : ℝ}(h:1≤q): q ≤ rangePay d q := le_self_pow₀ h (by omega)
lemma refund_one (d : ℕ){q : ℝ}(h:1≤q): 1≤refund d q:= one_le_pow₀ (h.trans (price_q d h))

lemma enormous_space : 0 < H.space P K := by
  let S : StepData (1:Side) ((1:Side)*P.L):= ⟨P,K,rfl⟩
  have hp : Nonempty (Forest S.ratio):= Tree.select S.ratio P.odd_side; exact H.space_pos (Classical.choice hp)

-- fixed expenses except P and K (view finish event after L)
def roofs (H : Budget G A (d+3)) := Fintype.card Axis * Inputs.variation G H.leaf ^ 2
lemma roof_nn (H : Budget G A (d+3)):0≤roofs H:= by unfold roofs; positivity
def skies (q : ℝ) := roofs H * (q^d)^2
def spice (q : ℝ) := q^2*(skies H q+1)
lemma skies_nn (q : ℝ): 0≤ skies H q:= mul_nonneg (roof_nn ..) (by positivity)
lemma spice_nn (q : ℝ):0≤ spice H q:= mul_nonneg (by positivity) (add_nonneg (skies_nn ..) (by simp))
def debit (q : ℝ) := ((acres P d : ℝ) + q^d)* spice H q - q⁻¹*(rangePay d q/(4*H.pale))^2

lemma gains : ∀ᶠ q:ℝ in atTop,debit H P q ≤ -q^2:= by
  let k:=(4*H.pale)⁻¹; let a:ℝ:=acres P d
  let u:=roofs H
  have hu : 0 ≤ u:= roof_nn H; have hp := H.law.1; have ha : 0 ≤ a:= by unfold a; positivity
  have hk : 0 < k := by unfold k; positivity; -- enough pay M^?
  let y:=(a+1)*(u+1)+1
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop (y/k^2)] with q hq h
  have hh : 0<q:= zero_lt_one.trans_le hq
  let p := q^(3*d+2); have hd : q^2 ≤ p:= pow_le_pow_right₀ hq (by omega); have hQ:=one_le_pow₀ (n:=d) hq
  have ht : skies H q+1 ≤ (u+1)*(q^d)^2:= by rw [add_mul]; apply add_le_add le_rfl; rw [one_mul]; exact one_le_pow₀ hQ
  have hM : (a + q^d) * spice H q ≤ (a+1)*(u+1)*p:= by
    have h' : a+q^d ≤ (a+1)* q^d:=by rw [add_mul,one_mul]; exact add_le_add_left (le_mul_of_one_le_right ha hQ) _
    apply (mul_le_mul h' (mul_le_mul_of_nonneg_left ht (sq_nonneg q)) (spice_nn H q) (by positivity)).trans_eq
    unfold p; ring
  have hG : y ≤ q*k^2 := (div_le_iff₀ (by positivity)).mp h
  have hw : q * y * p ≤ (rangePay d q*k)^2:= by
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG hh.le) (show 0≤p from (sq_nonneg q).trans hd)).trans
    unfold p; rw [mul_pow, show q*(q*k^2)*q^(3*d+2)= q^(2+(3*d+2))*k^2 by rw [pow_add q 2]; ring,rangePay,← pow_mul]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq (by omega)) (sq_nonneg k)
  have he : y*p ≤ q⁻¹*(rangePay d q/(4*H.pale))^2:= by rw [le_inv_mul_iff₀ hh,div_eq_mul_inv,← mul_assoc]; exact hw
  unfold debit; unfold y at *; unfold a u at *; linarith only [hd,hM,he]

lemma giving : ∀ᶠ q:ℝ in atTop,
    tableFare G P K M d * rangePay d q^(d+1) ≤ refund d q ∧
    holdRequest P M (rangePay d q) d ≤ refund d q:= by
  let k:= park (belt P)*(2*M)
  have hm :0 ≤ k:=by unfold k; positivity [park_nn (belt P), zero_le_one.trans (H.income_one P K)]
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop (tableFare G P K M d),eventually_ge_atTop (k+1)] with q hq he h
  let x:= rangePay d q; have hX : q≤x:= price_q d hq; have hx:=hq.trans hX
  constructor
  · refine (mul_le_mul_of_nonneg_right (he.trans hX) (pow_nonneg (zero_le_one.trans hx) _)).trans ?_; unfold refund; change x * x^(d+1)≤ x^_; rw [← pow_succ']; exact pow_le_pow_right₀ hx (by omega)
  change 1+x^d*park (belt P)*(2*M* x^(d+2)) ≤ x^(d+d+3)
  rw [show x^d*_* (2*M*x^(d+2))=k*x^(d+d+2) by unfold k; rw [Nat.add_assoc, pow_add]; ring, show x^(d+d+3)=x*x^(d+d+2) from pow_succ' ..]
  calc _ ≤ (k+1)*x^(d+d+2):= by rw [add_mul, one_mul, add_comm (1:ℝ) (k*_)]; exact add_le_add_right (one_le_pow₀ hx) _
       _ ≤ _:= mul_le_mul_of_nonneg_right (h.trans hX) (pow_nonneg (zero_le_one.trans hx) _)

-- spare envelope includes 1 for pressure tests with mark not applying `proximity`. reserve count of powers of t can be increased by taking higher d.
structure Labels (b : ℝ) : Prop where
  meter : 1 ≤ Home.clock b
  price : tableFare G P K (H.income P K) d * rangePay d (Home.clock b)^(d+1) ≤ refund d (Home.clock b)
  printed : holdRequest P (H.income P K) (rangePay d (Home.clock b)) d ≤ refund d (Home.clock b)
  deck : debit H P (Home.clock b) ≤ -(Home.clock b)^2
  walks (t : ℝ)(ht : Span b t) :
      t⁻¹ * rangePay d (Home.clock b) ≤ dial A ∧ t⁻¹*rangePay d (Home.clock b) ≤ H.space P K ∧
      t⁻¹* rangePay d (Home.clock b)/(4*H.pale) ≤ H.glow
  chips (t:ℝ)(ht:Span b t):
    (1 + proximity G P M t (rangePay d (Home.clock b)) d) * Real.exp (-(Home.clock b)^2) ≤ t⁻¹ ^ (5*d+5)
lemma assent : ∀ᶠ b:ℝ in atTop, Labels H P K b := by
  have hx := H.law.1; have hg0 := H.law.2.1; let y:= H.glow*(4*H.pale); let p:= 3*d+8; let i:= d+d+d+2; let k:=5*d+5
  obtain ⟨u,hu,hg⟩ := market_le G P (zero_le_one.trans (H.income_one P K)) d
  filter_upwards [infinite_meter.eventually_ge_atTop (1:ℝ),fund_small _ (dial_pos H.right) p,fund_small _ (show 0<y from mul_pos hg0 (by positivity)) p, fund_small _ (enormous_space H P K) p, infinite_meter.eventually (giving H P K),infinite_meter.eventually (gains H P), survives u hu (i+k)] with b hb hd hy ha hg' he hu'
  let Z:= rangePay d (Home.clock b); have hZ : 1≤Z:=hb.trans (price_q d hb)
  have ht(t) (h : Span b t): t⁻¹* Z ≤ H.space P K:=ha t h
  refine ⟨hb,hg'.1,hg'.2,he,fun t ht'=> ⟨hd t ht',ht t ht', (div_le_iff₀ (by positivity)).mpr (hy t ht')⟩,fun t ht'=>?_⟩
  have hp:0<t:=zero_lt_one.trans_le ht'.starts
  have hL : Z≤t:= by
    have h := (ht t ht').trans (H.space_small P K); apply le_trans ((inv_mul_le_iff₀ hp).mp h) (le_of_eq (mul_one _))
  refine (mul_le_mul_of_nonneg_right (hg t ht'.starts Z (zero_le_one.trans hZ) hL) (Real.exp_pos _).le).trans ?_
  rw [inv_pow, ← one_div, le_div_iff₀ (by positivity)]; refine le_trans (b:= u*t^(i+k)*Real.exp (-(Home.clock b)^2)) (le_of_eq ?_) (hu' t ht')
  unfold i k; rw [pow_add]; ring
end power
end YM.MatchingLedger.Kiosk
