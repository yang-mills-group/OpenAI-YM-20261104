import YM.FormalOPE.RG10.GaugeGear.Dust
/-!
 # Clock across single transmission. Positive grades age exponentially. Last constants not decapped.
 No estimates on multiple regulators nor multi-torus periods here. Use same symbol through. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.GaugeGear.PassBook
open Transit.Voyage Route HStein Transit Function PowerSeries Finset Real
open scoped Topology BigOperators Classical
variable {X : Type} {U J : ℕ → Type}
variable {W:Scale X U} {F:Tier}{O:Rally W} {V:Voyage U J} [∀ i,Fintype (U i)] [∀ i,Fintype (J i)] [∀ i,DecidableEq (U i)]
variable {G : ∀ i, Subring (Channel (U i))}
variable {γ R C :ℝ} {i b N r d δ:ℕ}
local notation "L" => W.Y C R
local notation "φ" => W.fade γ
variable (h: PassBook V W G F O R C γ δ b N r d)
variable {j k : ℕ} {P:Channel (U j)}
variable (hi : b ≤ k) (hj:k≤j) (he:j≤N)
include h hi hj he
variable (hz : P∈G j)(ht:Guard P r d)
local notation "C'" => L j
local notation "W'" i:max => V.yield i j P

omit hj in
lemma fade_age (ha:i∈Ico k j) : W.fade γ j (i+1) ≤ L i^δ * W.fade γ j i := by
 have hw := (mem_Ico.mp ha).1; have hu':= h.toHours.richAt (hi.trans hw); have hu :0 ≤ L i:=by linarith
 have hu1:0 ≤ φ j i:= W.fade_nn; have hi' := W.positive i; have ht' := W.positive (i+1);
 have hv : φ j (i+1)= exp (γ* W.ticks i (i+1))*φ j i := by
    unfold Scale.fade; rw [←exp_add, W.ticks_add (i+1) (i:=i) (N:=j)]; congr 1; ring
 rw [hv]; apply mul_le_mul_of_nonneg_right _ hu1; apply le_trans (exp_monotone (mul_le_of_le_one_left (W.ticks_pos (Nat.le_succ _)) h.small)); rw [W.ticks_exp]; apply (div_le_iff₀ ht').2; exact h.neighbor i (Ico_subset_Ico hi he ha)
-- only one equilibrium age at positive grade
omit hi hj he h [∀ i,Fintype (U i)] [∀ i,DecidableEq (U i)] in
lemma dock (j i:ℕ)(x:Grade)(ht:0<x.2): echo W γ x i * W.fade γ j (i+1)= W.fade γ j i:= by
 unfold echo Scale.fade; rw [if_pos ht,←exp_add]; congr 1; rw [W.ticks_add (N:=j) (i+1) (i:=i)]; ring

def tariff (δ d r:ℕ):= δ*expansive d r + δ
local notation "β" => tariff δ d r

def arrived (r δ d:ℕ):=(2*tariff δ d r+6)*loft r d +5
local notation "Kx" => arrived r δ d
variable (S : Finset Grade)(hw : S ⊆ items r d) (hu: upstairs r d⊆ S)
variable (W1 α : ℕ→ ℝ) (hx0:∀ i∈Icc k j,0 ≤ W1 i)(hj': W1 j=1)
variable (hc0:∀ i∈Ico k j,W1 (i+1)≤ (W.Y C R i)^δ* W1 i)
variable (ha0:∀ i∈Ico k j,0≤α i ∧ α i * W1 (i+1)≤ W1 i)
variable (ha:∀ i∈Ico k j,∀ y∈S,echo W γ y i ≤ α i)
include hz ht hx0 hj' hc0 ha0 ha hw hu
lemma supported : ∑ x∈ S, essence F O k (W' k) x ≤ W1 k * (C'^Kx)*(∑ x∈ S, essence F O j P x):= by
 have h0 := h.toHours.richAt ((hi.trans hj)); have hp0 :1 ≤ C':= by linarith
 have H' := zero_le_one.trans hp0;
 let E:= stairs r d; let p (i:ℕ) (x:Grade) := essence F O i (W' i) x; let B:=∑ x∈S,p j x; have hb : 0 ≤ B:= sum_nonneg fun x _=> essence_nn _ _ _ _
 have HB : (∑ x∈S, essence F O j P x)= B:= by simp only [B,p,V.sameHere];
 let θ:= C'^((2*β+6)*loft r d)*B;
 have hm i (hi' : i∈ Ico k j) (n:ℕ)(hn : n ≤ β) : (L i)^n ≤ C'^β:= by have hu := h.toHours.paid (hi.trans (mem_Ico.mp hi').1);exact (pow_le_pow_left₀ hu (W.sees R C h.base (mem_Ico.mp hi').2.le) n).trans (pow_le_pow_right₀ hp0 hn)
 have hh : ((S.card):ℝ) ≤ C'^2 := (Nat.cast_le.mpr (card_le_card hw)).trans ((le_of_eq (show (↑(items r d).card:ℝ)=↑(loft r d) from by unfold items loft; rw [card_product,card_range,card_range])).trans (h.clock.trans (pow_le_pow_left₀ (by linarith [h.rich]) (h.toHours.zees (hi.trans hj)) _))) -- inspect
 have hM : (↑(j-k):ℝ)≤ C'^2:= le_trans (le_of_eq (by rw [Nat.card_Ico])) (W.ticks_number h.toHours hi hj) -- rewrite term
 have he' : k∈ Icc k j:= mem_Icc.mpr ⟨le_rfl,hj⟩; have hx' := hx0 k he'
 let X' := 1+(↑(j-k):ℝ); have hT : 0≤ X':= by unfold X'; positivity
 have hq (y) (hy:y∈S): p k y ≤ W1 k*(X'*θ):= by
    have H'0 (a:Grade)(h:a∈S): p j a≤ B:= single_le_sum (f:=p j) (fun u _=>essence_nn _ _ _ _) h
    have H'1 i (h₂:i∈Ico k j) (a:Grade)(h₃:a∈S): p i a ≤ α i * p (i+1) a + C'^β*∑ b∈ E a, p (i+1) b:= by
       unfold p; rw [← V.approach (mem_Ico.mp h₂).2]
       have he1: i+1 ≤ j:= (mem_Ico.mp h₂).2; have hv := hi.trans (mem_Ico.mp h₂).1
       apply (h.words (Ico_subset_Ico hi he h₂) (keeping (h.powers.clip (hv.trans (Nat.le_succ i)) he) hz he1) (positions (h.ranks.clip (hv.trans (Nat.le_succ i)) he) ht he1) (hw h₃)).trans
       exact add_le_add (mul_le_mul_of_nonneg_right (ha i h₂ a h₃) (essence_nn ..)) (mul_le_mul_of_nonneg_right (hm i h₂ _ (by unfold tariff; omega)) (Finset.sum_nonneg (fun u _ => essence_nn _ _ _ u)))
    refine le_trans (Budget.jump  S E C' B α W1 (leverage r d) hb h0 hx0 hj' (fun i hh'=> le_trans (hc0 i hh') (mul_le_mul_of_nonneg_right (hm i hh' δ ((show δ ≤ β by unfold tariff; omega))) (hx0 _ (Ico_subset_Icc_self hh')))) ha0 hh hM (fun _ _=> staid.trans hu) (fun _ H' _ hh' => cost_order (hw H') hh') H'1 H'0 k he' y hy) ?_ -- inspect ordering infer implicitly
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hp0 (Nat.mul_le_mul_left _ (cost_le (hw hy)))) hb) hT) hx'
 -- finish upper sum
 let q:= W1 k*(X'*θ); have hB' : 0 ≤ θ:= mul_nonneg (pow_nonneg H' _) hb; have h' : 0 ≤ q:=by unfold q; positivity
 rw [HB]; apply (sum_le_sum hq).trans; rw [sum_const,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_right hh h').trans;
 calc
   _ ≤ C'^2 * (W1 k *(C'^3*θ)):= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by unfold X'; nlinarith [mul_le_mul_of_nonneg_right h0 (sq_nonneg C')]) hB') hx') (pow_nonneg H' _)
   _ = _:=by unfold θ arrived; rw [pow_add]; ring
end YM.FormalOPE.RG10.GaugeGear.PassBook
