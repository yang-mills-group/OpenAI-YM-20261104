import YM.MatchingLedger.Review.Matinee

/-!
# Read coefficient supply in each window on actual history

Arbitrary finite mixtures/vacuum/outgoing derivative can only be read with stencil licenses.
No assertion that the operator/mask family is such a stencil at *all* its scales.
Run generic producer first; later transport field grammar in separate module.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Review
open Function Filter Set MeasureTheory Lattice RG Wilson Tree Pressure
open Precision Action Top Home Cooling Gazette Periodical Kiosk Books Push.Uniform
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff Finset
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio) (O : F.Slice G→ℝ)

section forecasts
open Finset Books
variable {ι : Type} [DecidableEq ι][Fintype ι]{V : ℕ→Books.Poly ι}(T : Fountain (V 0))(u : ℕ→Books.Poly ι)(t : ℝ)

def columnAt (n : ℕ): ℝ:= ∑ i∈antidiagonal n, FPS.report V T i.1 (u i.2)
def prospects (n:ℕ): ℝ:= ∑ i∈ Finset.range (n+1), t^i * columnAt T u i
lemma simultaneous (n : ℕ): prospects T u t n=∑ i∈antidiagonal n,t^i.2 * FPS.forecast T t i.1 (u i.2):=by
  have he (a : ℕ → ℝ) : (∑ i∈ range (n+1), a i) = ∑ i∈antidiagonal n, a i.2:= by
    rw [← Finset.Nat.sum_antidiagonal_swap]; exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i _=> a i) n).symm
  let p (a b:ℕ):ℝ:= t^b*(t^a*FPS.report V T a (u b))
  rw [prospects, he]
  simp_rw [columnAt,FPS.forecast_terms,Finset.mul_sum]
  refine Eq.trans (b:= ∑ i∈antidiagonal n,∑ j∈antidiagonal i.2, p j.1 j.2) (Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl (fun j hj=>?_)) (FPS.triple (fun _ b c=> p b c) n).symm
  rw [← mem_antidiagonal.mp hj,pow_add]; unfold p; ring

end forecasts

section accomplishments
open Finset
variable {A : ChartRatio G} {O} (s : S.Choices) (hB:S.patch.Branches S.kernel G)(hs : InRange S) (Y:Chip (Page G c))
    {U T c' t Z : ℝ} {d k M l}{P : Finset F.Free}
    (H : Budget G A (d+3))(H' : Dated (S:=S) d H Y t Z U c' T)(Q : Affords F P O k M) (h:k ≤ d)(hP:P.card≤l)
local notation "V" => edition F s A Y
local notation "g" => t⁻¹
local notation "W" => stamp F s hB hs A Y
local notation "Ψ" => weigh (F.order G) (Cooling.weight F (runway (t⁻¹ • Y)) t)

def annotation (G:Gauge)(k d : ℕ)(T M : ℝ)(l:ℕ) := ∑ j∈antidiagonal k, M*(height G l : ℝ)^j.2 * FPS.bill d T j.1 j.2

include H' Q h hP
lemma achievement :
    ‖Ψ (Affords.oneWord F A t k O) - prospects W (model F O) g k‖ ≤ annotation G k d T M l * (t⁻¹)^(k+1) := by
  have ht:= H'.fire; have hb : 0≤T:= (zero_le_one.trans ((license_earn F s hB hs Y H d (by omega) Z H'.earn H'.background H'.unit).one))
  have hm := Q.pos; have he:0≤ g:= inv_nonneg.mpr (zero_le_one.trans ht)
  have hv := (license_earn F s hB hs Y H d (by omega) Z H'.earn H'.background H'.unit).one
  let L:= pigment F hB Y A t
  have hx : Ψ (Affords.oneWord F A t k O)=∑ j∈ antidiagonal k, g^j.2 * L (model F O j.2):=by
    change L (∑ i∈ Finset.range (k+1),_) =_; rw [← Finset.Nat.sum_antidiagonal_swap]; simp_rw [_root_.map_sum,_root_.map_smul,smul_eq_mul]; exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i _=>_) _).symm
  rw [hx, simultaneous, ← Finset.sum_sub_distrib]; unfold annotation
  apply (norm_sum_le ..).trans; rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro j hj
  let B:= FPS.bill d T j.1 j.2; have hB':0 ≤ B:= pow_nonneg (zero_le_one.trans (FPS.board_one d hv)) _
  have heq:= mem_antidiagonal.mp hj
  have hk := (solar F s hB Y j.1 d H hs H' _ _ (capModel F O j.2) (by omega)).1
  rw [← mul_sub ((g)^_),norm_mul,Real.norm_of_nonneg (pow_nonneg he _)]
  have ha:= hk.trans (mul_le_mul_of_nonneg_right (Q.tokens F (show j.2 ≤ k+1 from by omega) l hP) (show 0≤B*(g)^(j.1+1) from mul_nonneg hB' (pow_nonneg he _)))
  refine (mul_le_mul_of_nonneg_left ha (pow_nonneg he _)).trans_eq ?_; rw [← heq, Nat.add_right_comm,pow_add (t⁻¹) (j.1+1)]; ring

lemma column_price : ‖columnAt W (model F O) k‖ ≤ annotation G k d T M l:= by
  apply (norm_sum_le ..).trans; apply Finset.sum_le_sum; intro j hj
  let B:= FPS.bill d T j.1 j.2
  have heq:= mem_antidiagonal.mp hj
  have hv := (license_earn F s hB hs Y H d (by omega) Z H'.earn H'.background H'.unit).one
  exact (solar F s hB Y j.1 d H hs H' _ _ (capModel F O j.2) (by omega)).2.trans <| mul_le_mul_of_nonneg_right (Q.tokens F (by omega) l hP) (show 0≤ B from pow_nonneg (zero_le_one.trans (FPS.board_one d hv)) _)

-- keep possible arbitrary budgets, before using actual-bit request
variable {R : Support c} (hp : P⊆located (area F) R)
local notation "r" => t⁻¹ * Z
include hp
omit h hB hs in
lemma sample_script (hB' : S.patch.Branches S.kernel G) :
  ‖Ψ O- Ψ (Affords.oneWord F A t k O)‖ ≤ M* Z^(k+1)*(t⁻¹)^(k+1)+ Affords.doorway G M l k*Real.exp (R.card * U - c'*(Z/(4*H.pale))^2):=by
  have hh : 1≤Z:= H'.earn; have ht : 1≤t:= H'.fire; have ha:0<t⁻¹:= inv_pos.mpr (zero_lt_one.trans_le ht)
  have he : Envelope O:= ⟨Q.meas,M,Q.high⟩; have hw := weight_pass F (runway (t⁻¹ • Y)) t hB'
  let f:= Affords.oneWord F A t k O; have hv:Envelope f:= run_pass ..
  rw [← weigh_sub hw.toEnvelope he hv]
  refine blister (A:=fieldTest F R ((r)/4)) hw ((Envelope.const c').mul (bounded F R t)) (envelope_sub he hv) (by positivity [Q.pos]) (Q.doorway_pos F l) ?_ (Q.doorway_left F ht le_rfl · l hP) ?_ (H'.calm F R)
  · intro v hv; apply Q.calculated F hp hh ht H'.sky le_rfl v; exact inside_cov F G (show (r)/4 ≤ (r) by apply div_le_self (by positivity) (by norm_num)) hv
  intro v hv; exact mul_le_mul_of_nonneg_left (recoil F d H ht hh H'.shrink hv) H'.q_pos
end accomplishments

variable {A : ChartRatio G} (C : Family G)(h:Front C)(hr:C.Makes)(δ : ∀ d, Budget G A (d+3))(hp:Pins.Prepared (province A δ) C.path.levels)
variable (m p : ℕ)
local notation "q" => ruler C m
local notation "t" => frost C m p
local notation "S"=> Top.stepTor C m p
variable {d k l : ℕ}{M : ℝ}(Y:Chip (Page G (C.side m p)))(hd : d ≤ C.path.levels.clock.J (m+1))
    (hY:‖Y‖≤ ruler C m^d)(R : Support (C.side m p))(hR:(R.card:ℝ)≤ acres (stepTor C m p).patch d+(ruler C m)^d)
local notation "Z" => rangePay d (ruler C m)
local notation "T" => refund d (ruler C m)
include h hr hp hd hY hR

omit hY in
lemma tail : Real.exp (R.card * spice (δ d) q - q⁻¹*(Z/(4* Budget.pale (δ d)))^2) ≤ (t)⁻¹^(5*d+5):= by
  let b:=C.path.levels.clock.hatBeta (m+1); let e:=(R.card:ℝ)*spice (δ d) q - (q)⁻¹*(Z/(4* Budget.pale (δ d)))^2
  have hh := finance C m p δ hp d hd; let f:= proximity G (S).patch ((δ d).income (S).patch (S).kernel) t Z d
  have hQ:1≤q:= hh.meter
  have ht:= zone C m p h hr
  change Real.exp e ≤ _; apply le_trans ?_ (hh.chips t ht); apply le_trans (b:=Real.exp (-(q)^2)); apply Real.exp_monotone; exact (le_trans (sub_le_sub_right (mul_le_mul_of_nonneg_right hR (spice_nn (δ d) q)) _) hh.deck)
  have hf:0≤f:=prox_ge G (S).patch (zero_le_one.trans ht.starts) (zero_le_one.trans ((δ d).income_one ..)) (zero_le_one.trans (hQ.trans (price_q d hQ))) _
  exact le_mul_of_one_le_left (Real.exp_pos _).le (le_add_of_nonneg_right hf)

-- keep growing horizon/all regulator inequality in one reusable rule. Can be instantiated eventually for uniform bounds.
def ticket (G : Gauge) (d k l:ℕ)(M v : ℝ):= M * (rangePay d v)^(k+1) + Affords.doorway G M l k + annotation G k d (refund d v) M l
lemma applied (hk:k≤d)(F:Forest (stepTor C m p).ratio)(s:(stepTor C m p).Choices)
    {O:F.Slice G →ℝ}{P:Finset F.Free}(hx:Affords F P O k M)(hh:P⊆located (area F) R)(he:P.card≤l):
    let T':= stamp F s (C.path.levels.blocks m p).branches (ensures C m p h) A Y
    ‖weigh (F.order G) (Cooling.weight F (runway ((Top.frost C m p)⁻¹ • Y)) t) O - prospects T' (model F O) (Top.frost C m p)⁻¹ k‖ ≤
       ticket G d k l M (ruler C m) * ((Top.frost C m p)⁻¹)^(k+1) := by
  let H:= ensures C m p h; let g:= (t)⁻¹
  intro T'; have hD:= dated C m p δ h hr hp d Y hd hY
  have hz:= tail C h hr δ hp m p hd R hR
  have hT := achievement F s (C.path.levels.blocks m p).branches H Y (δ d) hD hx hk he
  have hw := sample_script F Y (δ d) hD hx he hh (C.path.levels.blocks m p).branches
  have hv:=zone C m p h hr
  apply (norm_sub_le_norm_sub_add_norm_sub ..).trans ((add_le_add hw hT).trans ?_)
  rw [ticket,add_mul,add_mul]; apply add_le_add _ le_rfl; apply add_le_add le_rfl _
  exact mul_le_mul_of_nonneg_left (hz.trans (pow_le_pow_of_le_one (inv_nonneg.mpr (zero_le_one.trans hv.starts)) (inv_le_one_of_one_le₀ hv.starts) (by omega))) (hx.doorway_pos F l)
end YM.MatchingLedger.Review
