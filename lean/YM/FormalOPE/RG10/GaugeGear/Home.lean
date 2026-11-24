import YM.FormalOPE.RG10.GaugeGear.Ages
/-!
 # Form normalized perturbative kernel transport (not physical comparison)
 arbitrary ranks, no moment loss, age retention, acceptable landmarks.
 This is *all lengths*, provided the Hours & Gauge.W supplies hold at every step used.
 Includes warm sign/center/phase-step estimates ONLY if same Weight. Not perturbative convergent
 as k→∞ NOR physics. Applications to Regul commit need supplies for V representing A or I° etc.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.GaugeGear
open Route HStein Transit Transit.Voyage Function Finset PowerSeries
open scoped Topology BigOperators Classical
variable {X : Type} {U J : ℕ → Type}
variable {W:Scale X U} {F:Tier}{O:Rally W} {V:Voyage U J} [∀ i,Fintype (U i)] [∀ i,Fintype (J i)] [∀ i,DecidableEq (U i)]
variable {G : ∀ i, Subring (Channel (U i))}
variable {γ R C :ℝ} {i b N r d δ:ℕ}
variable (h: PassBook V W G F O R C γ δ b N r d)
local notation "L" => W.Y C R
local notation "φ" => W.fade γ
variable {j k : ℕ} {P:Channel (U j)}
variable (hi : b ≤ k) (hj:k≤j) (he:j≤N)
variable (hz : P∈G j)(ht:Guard P r d)
namespace PassBook
local notation "μ" => L j ^ arrived r δ d
local notation "W'" i:max => V.yield i j P
omit [∀ i,DecidableEq (U i)] [∀ i,Fintype (U i)] in
private lemma hx (i) : 0≤ audible O i:= fun a=> (O.read i).sign (W.point i a)
include h hi hj he hz ht
lemma family : F.gain (audible O k) (V.yield k j P) r ≤ μ * F.gain (audible O j) P r:= by
 have hf := h.supported hi hj he hz ht (items r d) (Subset.rfl) (filter_subset ..) (fun _=>1) (fun _=>1) (fun _ _=> zero_le_one) rfl (fun _ ht=> by rw [mul_one]; exact one_le_pow₀ (le_trans (by norm_num) (h.toHours.richAt (hi.trans (mem_Ico.mp ht).1)))) (fun _ _ => by simp) fun i _ a _=> echo_self h _ _
 unfold essence at hf; rw [grains F _ (hx k) _ (positions (h.ranks.clip hi he) ht hj), grains F _ (hx _) _ ht,one_mul] at hf; exact hf
lemma dynasty : F.gain (audible O k) (decap (V.yield k j P)) r≤ φ j k *μ* F.gain (audible O j) (decap P) r:= by
 let a := fun i => φ (i+1) i; have H (i) :a i= echo W γ (0,1) i:= Eq.symm (if_pos zero_lt_one)
 have hf := h.supported hi hj he hz ht (upstairs r d) (filter_subset ..) (Subset.rfl) (φ j) a (fun i _=> W.fade_nn) (by simp [Scale.fade]) (fun _ ht=>h.fade_age hi he ht) (fun i _=>⟨W.fade_nn,( (congr_arg (· * φ j (i+1)) (H i)).trans (dock j i (0,1) (by decide))).le⟩) (fun _ _ a h' => le_of_eq (if_pos (mem_filter.mp h').2))
 unfold essence at hf; rw [grains_non F _ (hx _) _ (positions (h.ranks.clip hi he) ht hj), grains_non F _ (hx _) _ ht] at hf; exact hf
-- enlarge δ for Hours & downstream event powers
omit h hi hj he hz ht
variable {T:Lens W.tape}{n:ℕ}
omit [∀ i,Fintype (U i)] [∀ i,DecidableEq (U i)] in
lemma moved (h:Hours W R C δ b N){δ':ℕ}(hi:δ ≤ δ') : Hours W R C δ' b N:= {
 rich:=h.rich, base:=h.base,
 neighbor:= fun i hi'=> (h.neighbor i hi').trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_trans (by norm_num) (h.richAt (mem_Ico.mp hi').1)) hi) (W.positive _).le)
 year:=fun i hi'=> (h.year i hi').trans (pow_le_pow_right₀ (le_trans (by norm_num) (h.richAt (mem_Ico.mp hi').1)) hi) }
lemma grant (h: V.regular W r d n i R) (hh : R ≤ C): V.regular W r d n i C := by
 exact { toEligible:= h.toEligible
         width:= by have he:= h.width; exact ⟨he.hi.trans hh, he.over.trans hh,he.fac_rank.trans hh,he.heat.trans hh,he.ticket.trans hh,he.markers.trans hh,he.trees.trans hh,he.mix.trans hh⟩
         order:=h.order.trans hh
         fee:=fun j hj i=> (h.fee j hj i).trans hh
         covariance:=fun i=> (h.covariance i).trans hh
         shifts:=fun j=> (h.shifts j).trans hh }
lemma arranged (h: PassBook V W G (Tier.pol n) (Rally.native W T) R C γ δ b N r d)
   (hr:∀ i∈Ico b N,V.regular W r d n i (L i ^ δ)) : Regular V W R C (δ+arrived r δ d) b N r d n G T:= {
 toHours:= moved h.toHours (by omega)
 fund:=fun i H'=> grant (hr i H') (pow_le_pow_right₀ (le_trans (by norm_num) (h.toHours.richAt (mem_Ico.mp H').1)) (by omega))
 selfish:=h.powers
 stable:=fun _ H' j HH p h₁ h₂=> by
    obtain ⟨hk,_⟩:= mem_Icc.mp H'; obtain ⟨hj,he⟩:= mem_Icc.mp HH; have H:= h.family hk hj he h₁ h₂
    rw [Tier.gain_classical _ (hx _), Tier.gain_classical _ (hx _)] at H; exact H.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_trans (by norm_num) (h.toHours.richAt (hk.trans hj))) (by omega)) (W.nn ..)) }
end PassBook
end YM.FormalOPE.RG10.GaugeGear
