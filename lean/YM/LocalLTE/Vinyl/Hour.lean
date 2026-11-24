import YM.LocalLTE.Vinyl.Front
import YM.LocalLTE.Rate.Permit
/-! Root skeleton bill with independent coefficients, permits at true Path not homogeneous marker. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette

open Merge.Palette Gas Ursell Bakers
open Greenbelt
set_option quotPrecheck false
attribute [local instance] Gauge.frobInner
variable {ι:Type}(M:ι → Lotus.Leaf R) (φ:ι→ Config G f→ℝ) (H:Cash W t μ L Q o a T R)(χ:Chi)
-- Every label.Energy in θ ledger same geometry.T.Z.T.Tag projection Ward.
local notation "Oz"=> Merge.Tickets (Merge.Palette.sign M S)
local notation "Y₀"=> radiusB t
variable (z:H.fragrances)(D:Captain.Oscars M z) {θ ι' J:ℕ}
local notation "Ux"=> (fun k=> z.snd k)
local notation "U₀"=> Captain.reachability (H:=H) z
local notation "M₀"=> (fun i=> East.docket H z i)
local notation "q₀"=> (fun k=> Captain.quietR M (z.2 k) (D k))
variable {α C B' v₁ d v₀ e A β κ :ℝ}(q n k :ℕ)(r₀:ℕ→ℕ)(A':ι→Prop)(hx:Candor M z D q n r₀ A')



-- Whorl.S e_a first variant C. v ~ -(1/2), power requires upper H(i,n) chosen from jumpFee grads.V.Uniform. use p length atMost.
local notation "EC"=> Directions G c
local notation "SC"=> Disk G c
open Sienna FrameBox Grove
open PhysicalNext.Repeat.East
-- Maneuvers depend on V generic. Carrier.P.Slot all.S.Fin count.Bound independent periods.

local notation "T!"=>betaF G t L
local notation "B₀"=> radiusB t
open Height
-- Boost.E.Tickets reserved marks.J shell nil acceptance.V.Template

def acclaim (x₀:ℝ)(tag:ℕ→ℕ) (R:Rep G f)(i:ℕ) := if R.activities.E i=0 then 1 else East.bloom x₀ (tag i)
local notation "vk"=> acclaim T! r₀ R
lemma crowned (p:ℕ)(κ:ℝ)(d:ℕ)(h:Coup.License p R κ (betaF G t L) r₀ d)(hp:1 ≤ T!) : Pumps R vk (1*incomingE G L t):=by
   have he:= h.bills; obtain ⟨hh,u,hp',hU⟩:=he
   have hz i: 1≤ vk i:= by unfold acclaim; split; rfl;exact hh _
   rw [one_mul,Coup.e_now L t (show 0 < T! from zero_lt_one.trans_le hp),← Coup.chip_zero]; refine ⟨hz,u,hp',fun i=> budget_mono (hU i) (fun j=> ?_) (fun j=>?_)⟩
   · split; next=> exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (zero_le_one.trans (hz _)) (hp' _|>.1))
     exact le_rfl
   split; next=>
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _); apply mul_le_mul_of_nonneg_right _ (hp' j|>.1); unfold acclaim; split; exact hh _; rfl
   rfl
variable (hB:1 ≤ betaF G t L)(hq:Q.rate < mini)
include hB H
-- lifts rank add.V.Zero all Others unused.D.Payment th.Stocks.
variable [Fintype ι] (L₁:ι→ℝ) (V:ℝ) (r:ι→ℝ)(aA:ι→ℝ)(hR:∀ i,r i=aA i*L₁ i)(hp':∀ i,0 ≤L₁ i)(hA:∀ i,1≤aA i)
-- Enough margin per scaled.Weight.Board.*
def Actor (X:Rep G f) (x:ℝ) (M:ι→Lotus.Leaf X)(r:ι→ℝ): Prop:=(∑ i,r i*X.p.mass (M i).crest (M i).weight) ≤ x^(-(1:ℝ))
omit H in
lemma spentZ (hr:∀ i,0 ≤ r i)(hv:Actor R (betaF G t L) M r) :
    (∑ i,mcount (S:=S) (G:=G) (L:=L) (s:=t) M r (acclaim (betaF G t L) r₀ R) q i* R.p.mass (M i).crest (M i).weight) ≤ Q.goal L t:=by
    let f:= T!
    have hp:0 < f:=zero_lt_one.trans_le hB
    have hz: 1≤ grow G L t:= Real.one_le_rpow hB (by norm_num)
    have h(i): mcount (S:=S) (G:=G) (L:=L) (s:=t) M r (acclaim (betaF G t L) r₀ R) q i≤ grow G L t*r i:=by
        unfold mcount; cases hx:(M i).turn with
        | logKey k=> have he:(M i).turn.blank R:= (M i).blank; rw [hx] at he
                     unfold Palette.sign; rw [hx]; change acclaim _ _ _ k*(grow G L t)^1*r i ≤ _; rw [acclaim,if_pos (show R.activities.E k=0 from he),one_mul,pow_one] -- change
        | gasKey k=> unfold Palette.sign;rw [hx]; change 1*((grow G L t)^0)*_≤_; rw [pow_zero,one_mul]; exact mul_le_mul_of_nonneg_right hz (hr _)
    have hθ : -(1:ℝ)+3/8 <Q.rate:=by linarith [Q.start]
    let m i:=R.p.mass (M i).crest (M i).weight
    refine le_trans (sum_le_sum (g:=fun i=>grow G L t * (r i*m i)) (fun i _=> ?_)) (le_trans (le_of_eq (Finset.mul_sum ..).symm) ((mul_le_mul_of_nonneg_left hv (zero_le_one.trans hz)).trans (?_)))
    · rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (h _) (mul_nonneg (Real.exp_nonneg _) (M i).profit)
    rw [mul_comm]; change f^(-(1:ℝ))* f^(3/8:ℝ) ≤ _; rw [← Real.rpow_add hp]; exact Real.rpow_le_rpow_of_exponent_le hB hθ.le
include hR hp' hA
lemma oldO (hp: Actor R T! M r) : (∑ i:ι,L₁ i* R.p.mass (M i).crest (M i).weight) ≤ Q.goal L t ∧ SumBudget (Merge.Palette.wages M L₁) 1:=by
   have hb:0 < T!:=zero_lt_one.trans_le hB
   let V i:= R.p.mass (M i).crest (M i).weight; have ht:0≤ Q.goal L t:= (Daisy.arable H).le; have hy i:(M i).weight ≤ V i:= R.p.loMass _ _ (Leaf.profit _)
   have hv: (∑ i,L₁ i*V i) ≤ Q.goal L t := by
      refine le_trans (sum_le_sum (g:=fun i=> r i*V i) (fun i _=> mul_le_mul_of_nonneg_right (show L₁ i≤r i from le_mul_of_one_le_left (hp' i) (hA i) |>.trans_eq (hR i).symm) (show 0≤V i from ((M i).profit.trans (hy i))))) (le_trans hp (Real.rpow_le_rpow_of_exponent_le hB (show -(1:ℝ) ≤ Q.rate by linarith [Q.start])))
   refine ⟨hv, budget_finite (fun i:ι=> mul_nonneg (hp' i) (Leaf.profit _)) ((sum_le_sum (fun i (_:i∈(univ:Finset ι))=> mul_le_mul_of_nonneg_left (hy i) (hp' i))).trans (hv.trans (Real.rpow_le_one_of_one_le_of_nonpos hB Q.stop.le)))⟩ -- defeq wages
omit hB H hR hp' hA
section tuning
lemma surveyA (ℓ k n m:ℕ)(θ:ℝ) : ∃ (α δ v τ θ' :ℝ) (q K j:ℕ), 0<K∧-(1/2:ℝ) < v ∧ v<Sienna.vow ∧ℓ<j∧ K≤j ∧ (∀ p:ℕ, p≤n → jumpFee q n m n k * ↑(p+1)+v*K ≤α) ∧ mini*q≤α ∧ α≤0 ∧ α<δ ∧ τ<0 ∧ (max ((1/2:ℝ)*j+(τ+v)*j) δ) +(v+(1/2-τ))*(ℓ:ℝ) < θ'∧ θ'<θ :=by
    let θ':=min 0 θ -1; let v:= -(15/32:ℝ); let τ:= -(1/8:ℝ); let δ:= θ'-((ℓ:ℝ)+1); let α:= δ-1
    obtain ⟨q,hq⟩:=exists_nat_gt (α/Pastel.mini); have hm':mini <0:=by norm_num [mini]
    have hq': Pastel.mini*q ≤α := by rw [div_lt_iff_of_neg hm'] at hq; linarith
    let f:ℝ:= jumpFee q n m n k*(n+1:ℕ); have hv:v<0:=by norm_num [v]
    obtain ⟨K,hK⟩:= exists_nat_gt ((α-f)/v)
    let χ:= (1/2:ℝ)+(τ+v); have hχ:χ<0:=by norm_num [χ,τ,v]
    obtain ⟨j,hj⟩:=exists_nat_gt (δ/χ); let d:=K+1; let J:=j+1+d+ℓ; have ht:d≤J ∧ j≤J ∧ ℓ < J:= by unfold J; omega
    refine ⟨α,δ,v,τ,θ',q,d,J,(by unfold d; omega),(by norm_num [v]), (by norm_num [v,Sienna.vow]),ht.2.2,ht.1,fun p hp=>?_,hq',(by unfold α δ θ'; linarith [min_le_left (0:ℝ) θ,Nat.cast_nonneg (α:=ℝ) ℓ]),(by linarith only [show α=δ-1 from rfl]),(by norm_num [τ]), ?_,(by unfold θ'; linarith [min_le_right (0:ℝ) θ])⟩
    · refine le_trans (add_le_add_left  (show _ ≤ f from ?_) _) ?_
      · unfold f; exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.succ_le_succ hp)) (by unfold jumpFee; positivity)
      have hh: K ≤ d:= by unfold d; omega
      rw [div_lt_iff_of_neg hv] at hK; nlinarith only [mul_le_mul_of_nonpos_left (Nat.cast_le (α:=ℝ).mpr hh) hv.le,hK]
    have hh (x:ℝ)(hx:x≤δ): x+(v+(1/2-τ))*ℓ < θ':= by unfold δ at hx; unfold v τ; linarith only [hx,Nat.cast_nonneg (α:=ℝ) ℓ]
    refine hh _ (max_le ?_ le_rfl); have h:= div_lt_iff_of_neg hχ |>.1 (lt_of_lt_of_le hj (Nat.cast_le.mpr ht.2.1)); unfold χ at h; linarith only [h]
end tuning
end YM.LocalLTE.Fan
