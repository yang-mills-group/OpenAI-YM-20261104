import YM.FormalOPE.RG10.Horizon.Rates

/-!
# Horizon and scale stability on formal coefficients from actual joined errors in the raw projection
No Gram assumptions except `Valid` *real unperturbed height* for tested far matrix. A and K masks
never proved irrelevant, absent in the shifted projection. Auxiliary controller law per query,
not summing any Taylor series over orders. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Clearing
open Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD Panel Panel.Consumer InversionTop
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle Arrangements Apertures Transit Route Capture Weave Film
open scoped Topology BigOperators ContDiff Classical
open PowerSeries Ledger Rates
variable {G:Gauge}{F:Frames G}{R:Rails F}{P:Plan F}{Y:Drivers}{Z:Patience P Y} {m r h d:ℕ}{s t α β:ℝ}

structure Tuned (R:Rails F)(Z:Patience P Y) : Prop where
  street : Street Z R
  smooth : ∀ n,Continuous (fun s=>coeff n (R.flow.psi s))
  regular d n (i j:Deck F d): Continuous (fun s=>coeff n ((R.route d).train s i j))

variable (T : Tuned R Z) (M:Apertures.Halo) (u:Fin m→Seats F d) (E:Fore m)
abbrev revenue (F:Frames G)(h:ℕ):= (Fintype.card (Deck F h):ℝ)
local notation "F₀" v => burst R Z v
variable (R Z) in
/-- Finite real WilsonX coefficient *prediction from far clock* (not any exact Theory Reader).
Row vector convention inverse on the right. -/
def winter (h:ℕ) (s:ℝ) := (fun i=> burst R Z (exhibit M i) s E u) ᵥ* (M.invertAt R Z h s)

local notation "T₁" => Deck F h
local notation "Y" i => (Deck.price F h i:ℝ)
local notation "v'" => winter R Z M u E h
variable {M E u}
include T
lemma supply (θ:ℝ)(hΘ:0<θ)(h r:ℕ)(M:Apertures.Halo): ∀ᶠ t:ℝ in atTop,∀ i j, coin r (M.invertAt R Z h t i j) ≤ tilt t (-((Deck.price F h j):ℝ)-θ):=by
 apply Filter.eventually_all.mpr; intro i; apply Filter.eventually_all.mpr; intro j
 have hp := M.expense_back (Z:=Z) T.smooth h (T.regular h) -- arguments
 apply discount (α := -((Deck.price F h j):ℝ)) ?_ (by linarith only [hΘ]); intro n _; rw [neg_neg]; exact hp n i j
variable (hM: Valid F h M)
include hM
lemma investor (hp:∀ i j, coin r (M.invertAt R Z h t i j) ≤ tilt t (-((Deck.price F h j):ℝ)-α))
    {x:Seats F h} (he:∀ i:Deck F h,coin r ((F₀ (exhibit M i)) t E u-imply R Z (exhibit M i) t h x) ≤ tilt t (h+β)) (j : Deck F h) :
    coin r (v' t j - x j) ≤ revenue F h * tilt t (h+β-α-(Deck.price F h j:ℝ)) := by
 let V:= (M.invertAt R Z h t); let p:= x ᵥ* M.Lens R Z h t; let q:= fun i:Deck F h=> burst R Z (exhibit M i) t E u
 have hx: p ᵥ* V=x:=by unfold p V; rw [Matrix.vecMul_vecMul,M.right R Z h t T.street hM, Matrix.vecMul_one]
 rw [(show ∀ j, winter R Z M u E h t j-x j=((q-p) ᵥ* V) j from fun j=>by rw [Matrix.sub_vecMul,hx]; rfl) j]; unfold vecMul dotProduct; apply (coin_fore ..).trans;
 apply le_trans (b:=∑ _:Deck F h, tilt t (h+β-α-(Deck.price F h j:ℝ))) (Finset.sum_le_sum ?_ ) ?_
 · intro i _; apply (coin_mul ..).trans; apply le_trans ?_ (show tilt t (h+β)*tilt t (-((Deck.price F h j):ℝ)-α)=_ from ?_).le;
   · rw [show (q-p) i=_ from Eq.symm (congr_arg (q i-·) (heartbeat R Z M t x i))]; exact mul_le_mul (he i) (hp i j) (coined _) tilt_pos.le
   rw [← tilted]; congr 1; ring
 simp [revenue]

-- Use all tests `X∈S` at all epochs simultaneously in this geometric precision claim. Needed
-- before comparing different inner heights/shapes, but doesn't imply uniformity over exteriors.
variable {S:Finset (Vantage F)} (A:Attaches R Z u E r h S)
    (hC:∀ i:Deck F h,exhibit M i∈ S)
include A hC
theorem captor : ∃ β:ℝ,0<β ∧ ∀ᶠ s:ℝ in atTop, ∀ t∈ Set.Icc s (s+1), ∃ L:Ledger F h,
    ∀ v ∈ ({s,t}:Finset ℝ),
    (∀ x∈S, coin r (burst R Z x v E u-imply R Z x v h L.article) ≤ tilt v (h+β+β)) ∧
    (∀ x,coin r (v' v x - L.article x) ≤ revenue F h * tilt v (h+β-(Deck.price F h x:ℝ))) := by
 obtain ⟨C,δ,α,hD,hE,HA⟩:= twins A; have H:0<α/3:=by linarith
 refine ⟨α/3,H,?_ ⟩;
 obtain ⟨p,hp⟩:= Filter.eventually_atTop.mp ((supply T _ H h r M).and (absorbed (p:=δ) (M:=C) (show (h:ℝ)+α/3+α/3 < h+α by linarith)))
 filter_upwards [eventually_ge_atTop p,HA] with s hs h0 t ht;
 obtain ⟨L,hl⟩:= h0 t ht; refine ⟨L, fun w hw=>?_⟩
 have hwp:w ≥ p:= by simp only [mem_insert,mem_singleton] at hw; rcases hw with rfl|rfl; exact hs; exact hs.trans ht.1
 have he(x)(hx:x∈S):= le_trans (hl w hw x hx) (hp w hwp).2
 refine ⟨he, fun x=> (investor (β:=α/3+α/3) T hM (hp w hwp).1 (fun i=> ?_) x).trans_eq ?_⟩
 · simpa only [← add_assoc] using he _ (hC _)
 rw [← add_assoc, add_sub_cancel_right]

lemma linkedin : ∃ α:ℝ,0<α ∧ ∀ᶠ s:ℝ in atTop, ∀ t∈ Set.Icc s (s+1), ∀ x, coin r (v' s x-v' t x) ≤ (2*revenue F h)*tilt s (h+α-(Deck.price F h x:ℝ)) := by
 obtain ⟨α,hu,he⟩:=captor T hM A hC -- fix case
 refine ⟨α,hu,?_⟩; filter_upwards [he] with s hs t ht x; obtain ⟨L,hl⟩:=hs t ht
 have hz : 0 ≤ h+α-(Deck.price F h x:ℝ) := by
     have hx:(Deck.price F h x:ℝ)≤h:=by exact_mod_cast Deck.price_bound F h x
     linarith
 calc
   _ = coin r ((v' s x - L.article x) + (L.article x - v' t x)):=by congr 1; abel
   _ ≤ _:= by
     apply (coin_add ..).trans; rw [coin_sub_rev (u:=L.article x)];
     apply le_trans (add_le_add (hl s (by simp) |>.2 x) ((hl t (by simp)|>.2 x).trans (mul_le_mul_of_nonneg_left (cooling ht.1 hz) (by unfold revenue; positivity))))
     linarith
end YM.FormalOPE.RG10.Clearing
