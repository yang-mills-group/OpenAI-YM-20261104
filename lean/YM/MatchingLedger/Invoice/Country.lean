import YM.MatchingLedger.Invoice.Leaves

/-!
# A physical coupling producer, one-step, at *arbitrary order* d

Full moment law on free-link patch logs `crawl` (at actual t, not hat t).
Cost includes exterior deterministic tilt Y, here at sup angle clock^d/t. Includes exact full
history Family on these steps, normalization & angle evaluations. No extension to arbitrary
coarse fields *estimated* by this module, no output connected/OPE claim here. Use for further
field-stencil transports.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Kiosk
open Function Filter Lattice RG Wilson Tree Pressure Pressure.Stores Precision Push.Uniform
open PatchArea Action Periodical Books Gazette Set Metric
open MeasureTheory
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff Finset
variable {G : Gauge} {A : ChartRatio G}
section REQ
variable {c f:Side}(S:StepData c f)(H : ∀ d, Budget G A (d+3))
def province (A:ChartRatio G)(H:∀ d:ℕ, Budget G A (d+3)) : Pins.After G where
  wants P K d b:= Labels (H d) P K b
  sustained _ P K _:= assent _ P K

include S in
lemma skies_bound {t q:ℝ} (ht:1≤t)(hq:1≤q){d:ℕ}{Y : Chip (Page G c)} (h:t⁻¹* rangePay d q ≤ 1)(he:‖Y‖≤q^d) (x : Site c) :
    t^2 * outside (runway (t⁻¹ • Y)) x ≤ skies (H d) q := by
  have ht' := zero_lt_one.trans_le ht
  let F:= Classical.choice (Tree.select S.ratio S.patch.odd_side)
  let a:ℝ:= t⁻¹*q^d; let Y':= t⁻¹ • Y; have hp : 0≤a:= by unfold a; positivity
  let z:= Sum.elim (0:Chip (Needle F G)) Y'; let Z : ℝ:= Inputs.variation G (H d).leaf
  have hv:‖z‖≤a:= joined 0 _ (norm_zero.trans_le hp) (by unfold Y'; rw [norm_smul_of_nonneg (inv_pos.mpr ht').le]; exact mul_le_mul_of_nonneg_left he (inv_pos.mpr ht').le)
  have hy:a≤1:= (mul_le_mul_of_nonneg_left (price_open d hq) (inv_pos.mpr ht').le).trans h
  have hV : venue F z=runway Y':= rfl
  have hz:0≤Z:= div_nonneg (Budget.leaf_pos ..).le G.colorScale_pos.le
  have hm(i) : G.chord (runway Y' (x,i))≤ Z*a:= by rw [← hV]; exact (Inputs.chord ((H d).violet F) (by omega) (hv.trans hy) (x,i)).trans (mul_le_mul_of_nonneg_left hv hz)
  unfold outside; apply le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (g:=fun _=>(Z*a)^2) (fun i _=> pow_le_pow_left₀ (G.chord_nonneg _) (hm i) _)) (sq_nonneg t)) (le_of_eq ?_)
  unfold skies roofs Z a; rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,mul_pow]; field_simp
end REQ

section capital
open Top Home
variable (C:Family G) (m p:ℕ) (δ : ∀ d:ℕ, Budget G A (d+3))
    (h : Front C) (hr:C.Makes)(hp:Pins.Prepared (province A δ) C.path.levels)
local notation "b" => C.path.levels.clock.hatBeta (m+1)
local notation "B" => (C.path.levels.clock.op m p)
local notation "P" => StepData.patch B
local notation "K" => StepData.kernel B
local notation "t" => Top.frost C m p
local notation "q" => ruler C m
include hr h
lemma zone : Span b t := by
  have hm:= h.issued m p; have hf:= (hr.wilson.represents (m+1) p (m+1) le_rfl).band; have he := frost_beta C m p hr
  exact ⟨hm.2.1,(he.symm ▸ hf.1),(he.symm ▸ hf.2)⟩
omit hr in

lemma ensures : InRange B:= (h.issued m p).2.2 -- omit hr

variable (d:ℕ) (Y : Chip (Page G (C.side m p)))(hd : d≤ C.path.levels.clock.J (m+1))
    (hY : ‖Y‖≤ruler C m^d)
local notation "H" => δ d
local notation "v" => refund d (ruler C m)
local notation "Z" => rangePay d (ruler C m)
local notation "M" => Budget.income H P K
local notation "f" => skies H q
include hp hd
omit hr h in
lemma finance : Labels (δ d) P K b:= hp m p d hd

include hY
lemma dated : Dated (S:=B) d (δ d) Y t Z (spice H q) q⁻¹ v:= by
  let R:= C.path.levels.clock.op m p
  let g:= frost C m p
  have hu:= finance C m p δ hp d hd; have hS:= zone C m p h hr; have hh:1≤ q := hu.meter
  have ht : 0 < g:=zero_lt_one.trans_le hS.starts
  have hM:= zero_le_one.trans (Budget.income_one H P K)
  have ht' := (h.issued m p).2.1
  obtain ⟨ht₀,hv,hE⟩:= hu.walks g hS
  have hp:0 < q:=zero_lt_one.trans_le hh
  have he :1≤ Z:= hh.trans (price_q d hh)
  refine ⟨hS.starts,he, hY.trans (price_open d hh),ht₀,hv,hE,hu.price,hu.printed,spice_nn H q,(inv_pos.mpr hp).le,?_,?_⟩
  · let k := proximity G P M g Z d; let e:=(acres P d:ℝ)*spice H q- (q)⁻¹*(Z/(4*Budget.pale H))^2
    have hg : k* Real.exp e ≤ (1+k)*Real.exp (-(q)^2):= by
      have hp':0≤ q^d:= pow_nonneg hp.le _
      apply mul_le_mul (le_add_of_nonneg_left zero_le_one) _ (Real.exp_pos _).le (add_nonneg zero_le_one (prox_ge G P ht.le hM (zero_le_one.trans he) _)); apply Real.exp_monotone; apply le_trans («b»:=debit H P q) _ hu.deck; exact sub_le_sub_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hp') (spice_nn H q)) _
    exact hg.trans ((hu.chips _ hS).trans (pow_le_pow_of_le_one (inv_pos.mpr ht).le (inv_le_one_of_one_le₀ ht') (by omega)))
  intro F W; exact h.cooled m p F _ W _ (skies_nn H q) (skies_bound B δ («t»:=g) ht' hh (le_trans hv (Budget.space_small H P K)) hY)

variable (F : Forest (stepTor C m p).ratio)(s : (stepTor C m p).Choices)
-- notation `.stamp` implicit `(stepTor C m p)`. provider: declare here then use!
local notation "V" => edition F s A Y
local notation "cooked" => Cooling.weight F (runway ((Top.frost C m p)⁻¹ • Y)) t
local notation "Φ" => stamp F s (RG.Calendar.BlockControl.branches (C.path.levels.blocks m p)) (ensures C m p h) A Y

lemma headline (k l:ℕ) (u : Books.Poly (Needle F G)) (hu:u.totalDegree≤l) (hk:k+l≤d) :
    ‖weigh (F.order G) cooked (Periodical.run F A t u) - Books.FPS.forecast Φ (t)⁻¹ k u‖ ≤ fare u * (Books.FPS.bill d v k l *(t)⁻¹^(k+1)) ∧
      ‖Books.FPS.report V Φ k u‖ ≤ fare u* Books.FPS.bill d v k l:= solar F s (C.path.levels.blocks m p).branches Y k d (δ d) (ensures C m p h) (dated C m p δ h hr hp d Y hd hY) u l hu hk
end capital
end YM.MatchingLedger.Kiosk
