import YM.RG05Readout.Shadows.Stall
import YM.RG05Readout.Capture.Succ
/-!
# Budget and uniformity of the late loan by report sizes

Proof scalings with radius restored honestly through aperture. Mark support
witness is charged at exact root. Outer continuum readout/survival still needed
on this normalized Family.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Shadow
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets Copper View Address Many Pressure
open Legato Bandage Next.Rank.Station Accent Marker Menu Ac OPE Ribbons
open GridApprox.Nil Extra.Trajectories Extra.Multi
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G} {N m n b p d j:ℕ}{D:Address.Rail C}{B:ℕ→ℕ→ℝ}{x e E y:ℝ}
set_option quotPrecheck false
local notation "Z!"=> C.path.levels
local notation "R₀"=> C.path.rep N p
local notation "Ω"=> C.path.levels.clock.op
local notation "ζ"=> C.S.block
local notation "ν"=> C.path.levels.clock.J
local notation "κ"=> kappa C.path
local notation "Z₀"=> C.path.levels.budget
local notation "w₀"=> focus C E n
local notation "δ₀"=> renal C.path.levels
local notation "β"=> C.path.levels.clock.hatBeta
local notation "λ!"=> ld C.path.levels

-- Prices for real aperture only
noncomputable def threshold (C:Family G)(d n:ℕ)(e v t:ℝ):ℝ:= v/ (1+2*v*((fare C n d t e)))
noncomputable def safe (C:Family G) (d n:ℕ)(e v t:ℝ):ℝ:= 1+(((C.S.block n).val:ℝ)^d*((Bandage.renal C.path.levels n)*threshold C d n e v t)⁻¹)+ bid C n d (debit C n d t)+ bid C n d e
local notation "V'"=> threshold C d n e y x
local notation "V₁"=> safe C d n e y x
lemma bid_nn (he:0 ≤ e):0 ≤ bid C n d e:=by unfold bid; have hz:=lamp_nn (C:=C) n; positivity
lemma fare_nn (he:0 ≤ e)(hx:0 ≤ x):0 ≤ fare C n d x e:=by
    have hr:= lamp_nn (C:=C) n; have hy:= bid_nn (C:=C) (n:=n) (d:=d) he; unfold fare debit burden publicCost bling; positivity
lemma buys (he:0 ≤ e)(hy:0 < y) (hx:0 ≤ x): 0 < V' ∧ V' ≤ y ∧ 2*V'*fare C n d x e ≤ 1∧0< V₁∧focus C V₁ n n*((C.S.block n).val:ℝ)^d ≤ (renal C.path.levels n)*V'∧ (bid C n d (debit C n d x) ≤ V₁)∧ bid C n d e ≤ V₁:=by
    have ht:= fare_nn (C:=C) (n:=n) (d:=d) he hx; let F:= 1+2*y*(fare C n d x e); have hf:0<F:=by unfold F; positivity
    have hw:0<V':=div_pos hy hf; let S:= V₁; have hs:=lamp_nn (C:=C) n
    have hv:= bid_nn (n:=n) (C:=C) (d:=d) he; have hq :=bid_nn (n:=n) (C:=C) (d:=d) (e:= debit C n d x) (by unfold debit publicCost bling; positivity)
    have hδ:0< δ₀ n:= Real.rpow_pos_of_pos (zero_lt_one.trans ((Z!).fits.delayed _)) _
    let a:=(↑((ζ n).val):ℝ)^d * ((δ₀ n)* V')⁻¹; have ha : 0<a:=mul_pos (pow_pos (by positivity) _) (inv_pos.mpr (mul_pos hδ hw));
    have hs' : a ≤S∧bid C n d e≤S∧ bid C n d (debit C n d x)≤S:=by
       unfold S safe; unfold a; constructor <;> try constructor
       all_goals unfold a at ha; linarith only [hv,hq,ha]
    have hA:0<S:= ha.trans_le hs'.1; let v:= V'; refine ⟨hw,div_le_self hy.le (by change 1 ≤ F; unfold F; have ht':=mul_nonneg (a:= 2*y) (by positivity) ht; linarith only [ht']),?_,hA,?_,hs'.2.2,hs'.2.1⟩
    · change 2*(y/F)*_ ≤_; field_simp; unfold F; linarith only
    rw [focus,tab_one]; let B:=β n; have hB: 1 ≤ B:= (Z!).fits.delayed _|>.le; have hQ:=mul_pos hδ hw; have he := inv_anti₀ hA (le_mul_of_one_le_left hA.le (one_le_pow₀ (n:=4) hB)); apply le_trans (mul_le_mul_of_nonneg_right he (pow_nonneg (by positivity) _))
    have hx:=hs'.1; unfold a at hx; change _ * _⁻¹ ≤ S at hx; let l:= (↑((ζ n).val):ℝ)^d; have h:l/(δ₀ n * v) ≤ S:=by rw [div_eq_mul_inv]; exact hx
    refine (le_of_eq (show S⁻¹ * l=l/S from (by ring))).trans ((div_le_iff₀ hA).mpr (le_trans ((div_le_iff₀ hQ).mp h) (le_of_eq (mul_comm ..))))

section uniform
variable {E:Type} {l:Filter E} {P:E→ℝ} {n:E→ℕ} {e x y : E→ℝ} {a:ℝ}
variable (hw:Storage C D)(hG:G.Simple) (ht:Tendsto P l atTop)(hn:Height C.S l P n 1)
include hw hG ht hn
lemma lunar : RateIs l P (fun _i=> (λ! (n _i))) 0:=RateIs.of_sandwich (RateIs.const ht (c:=1) one_pos) ((payblock hw hG ht hn).pays ht) (Eventually.of_forall (fun _i=> lamp_nn _)) ((hn.grows.eventually (Many.shifts hw hG)).mono fun _i hi=>hi.1) ht
lemma debited (hx:RateIs l P x 0)(d:ℕ): RateIs l P (fun i=>debit C (n i) d (x i)) 0:=by
    have hv := ((RateIs.const (c:=16*(1+(Fintype.card (Letter d):ℝ))) ht (by positivity)).mul ((lunar hw hG ht hn).power 4)); have he:= height0 (banket C hG) hn
    exact (hv.mul (he.mul hx)).swap (by ring)
lemma bidding (hx:RateIs l P x 0)(d:ℕ): RateIs l P (fun i=>bid C (n i) d (x i)) 0:=by
    have ht':= (RateIs.const ht (c:=2) (by norm_num)).mul (lunar hw hG ht hn)
    exact (((RateIs.const ht (c:=1) one_pos).add ht' ht).mul hx).swap (by norm_num)
lemma fares_spent (he:RateIs l P e 0)(hx:RateIs l P x 0)(d:ℕ): RateIs l P (fun i=> fare C (n i) d (x i) (e i)) 0:=by
    have hs:= (RateIs.const ht (c:=2) (by norm_num)).mul he; have hz:= (RateIs.const ht (c:=20) (by norm_num)).mul (bidding hw hG ht hn he d)
    exact ((debited hw hG ht hn hx d).add (((lunar hw hG ht hn).power 2).mul (hs.add hz ht)) ht).swap (by norm_num)
lemma safely (hx:RateIs l P x 0)(he:RateIs l P e 0)(hy:RateIs l P y 0)(d:ℕ):RateIs l P (fun i=> safe C d (n i) (e i) (y i) (x i)) 0:=by
    have hh:= RateIs.const ht (c:=1) one_pos; have hY:=(((RateIs.const ht (c:=2) two_pos).mul hy).mul (fares_spent hw hG ht hn he hx d)); have hv:= (height0 (mintN C hG).1 hn).mul (hy.div (hh.add hY ht)); have hp:= (bidding hw hG ht hn (debited hw hG ht hn hx d) d); exact ((((hh.add (((payblock hw hG ht hn).power d).mul hv.inv) ht).add hp ht).add (bidding hw hG ht hn he d) ht)).swap (by norm_num)
omit hw hG
lemma focused (he:RateIs l P e 0)(b:ℕ): RateIs l P (fun i=> Shadow.focus C (e i) (n i) b) (1/3):=by
    let x(i):=Real.exp (-(C.S.scale (n i)-C.S.scale b)/3); have hx:RateIs l P x (-(1:ℝ)/3):=by
        refine ⟨Eventually.of_forall (fun i=>Real.exp_pos _), ?_⟩
        simp_rw [x,Real.log_exp]; have hq:= hn.pace.sub (show Tendsto (fun i=> C.S.scale b/P i) l (𝓝 (0:ℝ)) from tendsto_const_nhds.div_atTop ht); have hx:=(hq.const_mul (-(1:ℝ)/3)); rw [sub_zero, mul_one] at hx; apply hx.congr (fun i=> ?_); ring
    have hg:= (RateIs.const ht (c:=β b) (zero_lt_one.trans ((Z!).fits.delayed _))).power 4
    exact ((hg.mul (hx.mul he)).inv).swap (by ring)
end uniform
end YM.RG05Readout.Shadow
