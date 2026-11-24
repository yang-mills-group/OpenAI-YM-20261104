import YM.FormalOPE.RG10.Horizon.Fall

/-! # Existence and uniqueness of multi-insertion coefficients (formal carry at $X'$)

Recovered *solely* on diagrams, no theory-dependent Reader or correlation fitting. These are
for absolute center-bump conventions and centered-position geometry in `Footing.test`: unchanged
`burst R Z` throughout. Functions including Θ-free rules exactly as in these definitions; need
open gates and corridor estimates in `Attaches` on EVERY finite edition of coefficients used.
Extraction through order r requires no bigger perturbative order on these array approximation
estimates from Ledger.Fk. Still requires Test-fit in chosen Deck h matrix (existing
real-free detector budget `Survey.shines`). -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Clearing
open Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD Panel Panel.Consumer InversionTop
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle Arrangements Apertures Transit Route Capture Weave Film
open scoped Topology BigOperators ContDiff Classical
open PowerSeries Ledger Rates
variable {G:Gauge}{F:Frames G}{R:Rails F}{P:Plan F}{Y:Drivers}{Z:Patience P Y}{r m d h n:ℕ}
    (T:Tuned R Z) (M: Halo) (x:Fin m→ Seats F d)(E:Fore m)
local notation "v" => winter R Z M x E

variable (R Z) in
/-- Far coefficient of the fixed product/profile (definition common to all orders). Use ONLY
under the window hypotheses proving these limits exist. No claim for failed limits. -/
def profit (h:ℕ) (j : Deck F h) : fps := PowerSeries.mk (fun i=>limUnder atTop (fun t=>coeff i (v h t j)))
local notation "B" => profit R Z M x E
lemma corner (j:Deck F h)(n:ℕ) : coeff n (profit R Z M x E h j)=limUnder atTop (fun t=>coeff n (winter R Z M x E h t j)):=by simp [profit]
variable {M x E} (hM :Valid F h M){S:Finset (Vantage F)} (A: Attaches R Z x E r h S)(hC:∀ i:Deck F h,exhibit M i∈ S)
include A T hM hC
local notation "C'" => revenue F
local notation "Y₁" i:max => (Deck.price F h i:ℝ)

lemma account (j:Deck F h)(n:ℕ)(hn:n≤r) : Tendsto (fun t=>coeff n (winter R Z M x E h t j)) atTop (𝓝 (coeff n (B h j))) := by
 obtain ⟨_,_,H⟩:=payments T hM A hC; obtain ⟨b,hb,-⟩:=H j n hn; rw [corner, hb.limUnder_eq]; exact hb

omit T A hM hC in
lemma clearing_const (K:ℝ){α β:ℝ}(hp : α<β) : ∀ᶠ t in atTop, K*tilt t β≤ tilt t α:= by simpa only [cash,legUp,pow_zero,mul_one] using absorbed (M:=K) (p:=0) hp

theorem dividend : ∃ ζ:ℝ,0<ζ ∧ ∀ᶠ s in atTop,∀ i:Deck F h,
      coin r (B h i-v h s i) ≤ tilt s (h+ζ-Y₁ i):= by
 obtain ⟨α,hα,H⟩:=payments T hM A hC; refine ⟨α/4,by linarith,Filter.eventually_all.mpr (fun i=>?_)⟩
 have ht (n:ℕ) (hu:n≤r): ∀ᶠ s in atTop, ‖coeff n (v h s i)-coeff n (B h i)‖ ≤ tilt s (h+α/2-Y₁ i) := by
   obtain ⟨b,hb,C,hk,He⟩:= H i n hu
   rw [corner,hb.limUnder_eq]; filter_upwards [He,clearing_const C (show (h:ℝ)+α/2-Y₁ i< h+α-Y₁ i by linarith)] with s hs hr using hs.trans hr
 let xi:= (h:ℝ)+α/2-Y₁ i
 filter_upwards [Filter.eventually_all_finset (range (r+1)) |>.2 (fun n (hu:n∈Finset.range (r+1))=> ht n (by simpa using hu)),clearing_const (r+1) (show (h:ℝ)+α/4-Y₁ i< xi by unfold xi; linarith)] with s hs hs1
 · rw [coin_sub_rev,cstate]
   apply le_trans (b:=∑ _∈range (r+1), tilt s xi) (Finset.sum_le_sum ?_) _; swap
   · simpa using hs1
   simp_rw [map_sub]; exact hs

omit T A hM hC
-- cap cost of replacing a full mark in these absolute displays, nothing about joint contacts.
include T
lemma bill (X:Vantage F)(i:Deck F h)(r:ℕ) {ζ:ℝ} (hζ : 0 < ζ) : ∀ᶠ t in atTop, coin r (imply R Z X t h (seat i)) ≤ tilt t (Y₁ i-ζ):= by
 apply discount (α:=Y₁ i) ?_ (by linarith); intro n _; simpa only [tilt,neg_mul_neg] using! journey X T.street T.smooth (T.regular h) n i

-- all exterior estimates (forces ledger.printability); direct uses validity for pair only to pin.
include A hM hC
theorem awarded : ∃ ζ:ℝ,0<ζ ∧ ∀ᶠ t in atTop,∀ u∈ S,
     coin r (burst R Z u t E x-imply R Z u t h (B h)) ≤ tilt t (h+ζ):= by
 obtain ⟨β,hβ,h0⟩:= captor T hM A hC
 obtain ⟨ξ,hξ,F₀⟩:= dividend T hM A hC
 let ρ:= min β ξ; have hρ:0<ρ:=lt_min hβ hξ; have he:ρ≤β:=min_le_left ..; have hf:ρ≤ξ:=min_le_right ..
 have hh:0<ρ/2:=by linarith
 refine ⟨ρ/4,by linarith,?_ ⟩
 let α:=(h:ℝ)+ρ/2
 have hr : 0 ≤ C' h:=by unfold revenue; positivity
 have hc t := le_add_of_nonneg_right (a:=t) (show (0:ℝ)≤1 by norm_num)
 have HI:= Filter.eventually_all_finset S |>.2 (fun u _=> Filter.eventually_all.mpr (fun i:Deck F h=>bill T u i r hh))
 filter_upwards [h0, F₀, eventually_ge_atTop 0, clearing_const (1+ C' h*(C' h + 1)) (show ↑h+ρ/4<α by unfold α; linarith),HI] with t ht htF hp Hτ htI u hu
 obtain ⟨L,hl⟩:= ht t (Set.left_mem_Icc.mpr (hc t))
 obtain ⟨hl,hs⟩:=hl t (by simp)
 let V := imply R Z u t h; let X₁:= burst R Z u t E x; let X':Seats F h:=L.article- (B h);
 have hK : X₁-V (B h)=X₁-V L.article+V X':= by unfold X'; rw [map_sub]; abel
 change coin r (X₁-V _ ) ≤_; rw [hK]
 calc
   _ ≤ coin r (X₁-V L.article)+coin r (V X'):= coin_add ..
   _ ≤ tilt t α+ C' h*((C' h+1)*tilt t α):= add_le_add ((hl u hu).trans (shade (by unfold α; linarith) hp)) ?_
   _ ≤ tilt t (↑h+ρ/4):= (le_of_eq (by ring)).trans Hτ
 conv_lhs=> rw [seating X',map_sum]
 simp_rw [map_smul,smul_eq_mul]
 apply (coin_fore ..).trans; apply le_trans (b:=∑ _ :Deck F h, ((C' h+1)*tilt t α)) (sum_le_sum ?_) (by simp [revenue]);
 intro i hi
 have heJ : coin r (X' i)≤ (C' h+1)*tilt t (h+ρ-Y₁ i) := by
   apply (le_of_eq (congr_arg (coin r) (show X' i=L.article i-v h t i+(v h t i-B h i) from by unfold X'; rw [Pi.sub_apply]; abel))).trans
   apply (coin_add ..).trans; rw [coin_sub_rev (u:=L.article i),coin_sub_rev (v h t i) (B h i),add_mul,one_mul];
   exact add_le_add ((hs i).trans (mul_le_mul_of_nonneg_left (shade (by linarith) hp) hr)) ((htF i).trans (shade (by linarith) hp))
 exact (coin_mul ..).trans ((mul_le_mul heJ (htI u hu i) (coined _) (mul_nonneg (by linarith) tilt_pos.le)).trans_eq (by rw [mul_assoc,← tilted]; congr 2; unfold α; ring))

end YM.FormalOPE.RG10.Clearing
