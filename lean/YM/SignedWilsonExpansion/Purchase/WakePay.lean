import YM.SignedWilsonExpansion.Purchase.Paystation
import YM.SignedWilsonExpansion.Purchase.Solier
import YM.Trace.Physicalv2.GermPrices
/-! # Filter lift to compact Cohorts & superslacks.
This API works with UV then Period (ordered estimates), requesting
Anchor/Height before any limit. Proves projected arrivals' COSTS here
(not existence of such entries: see Grid). -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.SignedWilsonExpansion.Purchases
open Asymptotics PhysicalNext.Repeat.Quince.PreCost WilsonCoeffUV.Bank Function Filter Matrix Lattice RG Wilson Gauge Extra.Histories Analysis
open WilsonCoeffUV.Mer.Xa.FetchP Labels Trace.Physical.Germ Trace.Physical.GermGraph
open Source Work.G08 Next.Rank.Price Next.Rank Perch Commission Real
open scoped Classical ContDiff BigOperators Topology
variable {G:Gauge} {d l r:ℕ}{C:Family G}{F:Frame G d}{ι:Type}{Y W ν ρ B:ι→ℝ}{L:Filter ι}{j m n N p:ι→ℕ}
local notation "F₀" => (C.labels.level d)
local notation "H₀" => C.path
local notation "Θ"=> C.path.levels.clock.threshold
open PurchVoice UVClock YM.MergeProof YM.MergeProof.Ribbons
lemma toll0 (C:Family G)(d j p:ℕ): 0≤ tollQ C d j p:= mul_nonneg (invoice_nn ..) (zero_le_one.trans ( C.path.levels.params j|>.columns_ge))
lemma toll_isbelow (g:G.Simple)(n:ℕ): ∀ᶠ j:ℕ in atTop,∀ p, tollQ C d j p≤ (mark C.path.levels.clock.hatBeta j)^n:=by
    let t:=price (C:=C) d; let P(i):= mark C.path.levels.clock.hatBeta i; have H(i):P i= ( C.path.levels.clock.hatBeta i)^(-(1:ℝ)/2):=by rw[show -(1:ℝ)/2= -(1/2:ℝ) by ring,Real.rpow_neg (zero_le_one.trans (C.path.levels.fits.delayed i).le)]; unfold P mark; rw [Real.sqrt_eq_rpow]
    have ht:0<t:= mul_pos (by exact_mod_cast (Nat.zero_lt_succ _)) (germ_close _ _).choose_spec.1
    let v:= ((hut C g).powr (-(1:ℝ)/2)).powerN n; let Y:= ((Note.notes C.S t ht).mills (Note.bell_exp C.S (-1))).mills (fuNote C)
    filter_upwards [Y.outweigh v (by norm_num), cut_flat C g (-1)] with j hB hs p; change tollQ C d j p≤ ( P j )^n; rw [H]; exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hs p) ht.le) (zero_le_one.trans ( C.path.levels.params j|>.columns_ge))).trans hB
variable (hp: Rise B L)
include hp
lemma self_w (y:ι→ℝ): Wage L y 1 y:=⟨1, by simp; exact isBigO_refl _ L⟩
lemma spreadMax : Maxer L (Spread B):= (y_rise hp).eventually_ge_atTop 1
lemma dollarMax : Maxer L (dollar B):= (M_rise hp).eventually_ge_atTop 1
lemma ceases_w : cent B =O[L] (1:ι→ℝ):= isBigO_const_of_tendsto (θ_small hp) one_ne_zero
lemma mark_cent : mark B=O[L] cent B:=by
    refine IsBigO.of_bound' (hp.eventually (Paint.cooling (-1/2))|>.mono (fun i hi=>?_)); rw [Real.norm_of_nonneg (show 0≤ UVClock.cent B _ from (hedge _ _|>.le))]; exact hi -- need expo infer
variable (C:Family G)(g:G.Simple)
include g
lemma toll_w (ht:Epoch L B C.path.levels j)(n:ℕ)(d:ℕ)(p:ι→ℕ): (fun i=> tollQ C d (j i) (p i))=O[L] (fun i=> (mark B i)^n):=by
    apply IsBigO.trans _ ((( mark_tie hp ht ).isBigO).pow n); refine IsBigO.of_bound' ( ((Epoch.leaving hp C g ht ).eventually (toll_isbelow (C:=C) (d:=d) g n)).mono (fun i hi=>?_)); rw [Real.norm_of_nonneg (toll0 ..)]; exact (hi (p i)).trans (le_abs_self _)
lemma prec_w (ht:Epoch L B C.path.levels j)(d:ℕ)(p:ι→ℕ): Wage L (Spread B) (cent B) (fun i=> prec C d (j i) (p i)):=by
    refine Wage.plus (spreadMax hp) (Wage.enroll (IsBigO.trans ( toll_w hp C g ht 1 d p ) ?_)) (markS hp ht (-1/2)) ; simp only [pow_one]; exact mark_cent hp
variable (g':C.Makes) (hq:Epoch L B C.path.levels j)
include g' hq
-- no monotonic assertion for shrinking.But high-weight tuition uses `=O` when H ~B and θ/mark_s compares precisely
lemma ηPrice (p:ι→ℕ)(h:∀ᶠ i in L,j i≤ N i): Wage L (Spread B) ((dollar B)⁻¹) (fun i=> shrink C (j i) (N i) (p i)):= by
    let H(i):= C.path.levels.clock.hatBeta (j i); let U(i):= C.path.β (N i) (p i) (j i); let T := dnote C.path.levels ;
    have hx: (mark U)=O[L] (mark H):= ( ( mark_tie hp ( cutExposure hp C g g' hq p h ) ).trans (mark_tie hp hq).symm ).isBigO
    have hA: (mark U/mark H)=O[L] (1:ι→ℝ):=by
       apply IsBigO.congr' (hx.mul (isBigO_refl ((mark H)⁻¹) L)) (Eventually.of_forall (fun i=> (?_))) (Eventually.of_forall fun i=> (?_)); · exact div_eq_mul_inv ..|>.symm
                                                                               -- indent
       exact mul_inv_cancel₀ (show mark H i ≠0 from ne_of_gt (inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans ( C.path.levels.fits.delayed (j i))))))
    have hu(v:ι): shrink C (j v) (N v) (p v)=(mark U v/ mark H v) * (dollar H v)⁻¹:=by unfold shrink Calendar.threshold Calendar.hatCoupling; rw [T]; change _/(_*_) = (_/_)*_; ring
    have he:= Wage.mul (Wage.enroll (u:=Spread B) hA) ( Wage.mul ( markS hp hq (-1/2) ) ( markS hp hq (-1/2) ) ); refine Wage.fix he (Eventually.of_forall (fun i=>?_) ) (Eventually.of_forall (fun i=>?_))
    · dsimp only; rw [hu,penny]; rfl
    change 1*(cent B i*cent B i)=(dollar B i)⁻¹; rw[one_mul,penny]
lemma ηIP (p:ι→ℕ)(h:∀ᶠ i in L,j i≤ N i): Wage L (Spread B) ( dollar B) (fun i=> (shrink C (j i) (N i) (p i))⁻¹):=by
    have hm := Wage.mul (Wage.unitC (2:ℝ) (u:=Spread B) ( L:=L ) ) (markS hp hq 1) -- Wage.unitC order
    refine Wage.rel (Wage.fix hm ( .refl ..) ( by simp ) ) (?_); apply IsBigO.of_bound'; filter_upwards [h] with i hi; rw [Real.norm_of_nonneg (inv_nonneg.mpr (shrink_pos C g' hi (p i)).le)]; refine le_trans ( shrink_min C g' hi (p i) ) ?_; rw [dnote]; exact le_abs_self _
lemma phase_hats (p:ι→ℕ) (hm:Epoch L B C.path.levels m)(h:∀ᶠ i in L,m i≤ N i)(hq':∀ᶠ i in L,j i ≤ N i) : Tendsto (fun i=> phaseF C (j i) (m i) (N i) (p i)) L (𝓝 1):=by
    let y:= C.path.β; let v (i):= y (N i) (p i) (j i); let w(i):= y (N i) (p i) (m i)
    let H:= mark_tie hp (cutExposure hp C g g' hq p hq')
    let T:= mark_tie hp (cutExposure hp C g g' hm p h)
    apply (isEquivalent_iff_tendsto_one ?_).mp ( T.trans H.symm ); exact hq'.mono (fun i hi=> by exact ne_of_gt (inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive g'.wilson hi))))
-- utilize Filter.Ed.
end YM.SignedWilsonExpansion.Purchases
