import YM.RG05Readout.Halls.Cane
/-!
# End geometry and quantifier repayment

On this certified UV path: every fixed demand of Cartesian separated test
perforations in WM aperture, pays poly-at-all-recorded-companions even at
finite cutoff and ANY p supporting the orientations and signal locations.
Precision height costs not Taylor costs: x-trace computed numerically, not
retrospective scheme. Use when feeding limiting correlations. Doesn't assert
exchange with masks or near-diagonal matching. All powers in this transcript
for ACTUAL unnormalized Root products.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Halls
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion Cells Overlay
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons Ribbons.ManyCopies OPE
open Records Basket Shadow
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}{I J V:Type}[DecidableEq V][Fintype V]
    {j b k g ℓ t v:ℕ}
set_option quotPrecheck false
local notation "Θ"=> C.path.levels
local notation "λ₀"=> C.path.levels.clock
local notation "Z!"=> C.path.levels.budget
local notation "S!"=> C.S
local notation "s!"=> C.S.scale
local notation "P!"=> C.side b p
local notation "b!"=> C.S.a
variable (h:C.Makes){D: Address.Rail C} {ψ:ℕ→ℕ} {w:Worth} {B:ℕ→ℕ→ℝ}
    (Y:OPE.Package C w ψ D)(hC:Storage C D) (hS:Cater C D)(hG:G.Simple)
section
variable {E:Type} {l:Filter E}{T:E→ℝ}{m n:E→ℕ}{Q r:E→ℝ}{B' a η:ℝ}(ht:Tendsto T l atTop)(hm:Height C.S l T m 1)(hn:Height C.S l T n 1)(hN:∀ᶠ i in l, n i+1 < m i)(hQ:RateIs l T Q 0)(hR:∀ᶠ i in l, CaptureW C (n i+1) (m i) (r i) B')(hB:4 < B')
include hB hG ht hm hn hR
-- height stage after older margin. period-size event not needing limit p for B.Occ etc: eventually for all p simultaneously! Real readouts at even cutoff finite-size.This inequality in sphere units because `‖G! u‖` measured Euclidean.
local notation "β"=> C.path.levels.clock.hatBeta
local notation "Xn"=> fun i=> n i+1
omit hn ht
lemma family_fills (he:0<η) : ∀ᶠ i in l, 2*(b! (m i))*(1+((Z! (m i)).B:ℝ)^2)< η*r i:=by
   filter_upwards [hR,hm.grows.eventually (shelf (X:=Θ) hG (η:=η/2) (by positivity) hB)] with i hL hh
   let x:= b! (m i); have ha:0<x:= (S!).a_pos _
   have hz:= mul_lt_mul_of_pos_left hh ha
   have hv:=hL.lit.1; have ht': Lambda Θ (m i)=2+Real.log (β (m i)):=rfl
   have hp: 1≤ ((Z! (m i)).B:ℝ):=by exact_mod_cast (Z! (m i)).B_pos
   change 2*x*_ <_; let B:ℝ:= ((Z! (m i)).B); apply lt_of_le_of_lt (b:= x*2*(B^2)+x*2*(B^2)); swap
   · let L:= Lambda Θ (m i)
     have hv':x*L^ B' ≤ r i:= hv
     calc _ < x*(η/2*L^ B')+x*(η/2*L^ B'):=add_lt_add (by linarith only [hz]) (by linarith only [hz])
          _ = η*(x*L^B'):=by ring
          _ ≤ _:=mul_le_mul_of_nonneg_left hv' he.le
   linarith only [ha, mul_le_mul_of_nonneg_left (one_le_pow₀ (n:=2) hp) ha.le] -- check
include hn hN
local notation "d!"=> Fintype.card (Color V × Motion)
omit [DecidableEq V] in
lemma canKnock (b:ℕ)(s:V→ℕ) (hy:∀ i,s i ≤ ℓ)(hg:d ≤ ℓ) {t:ℕ} (hk:a≤t)(hw:∀ᶠ n in atTop, Warm C n (ℓ+1) k) (hp:0 ≤ a)(he:0<η) :
    ∀ᶠ i in l,∀ p:ℕ, ∀ (v:V→ Cover)(F:V→Body), (∀ j:V, ‖C.S.gridPoint (Xn i) (v j)‖ ≤ a*(C.S.a (Xn i))) → (∀ j,Cap (s j+2) (F j) 1) → carton C (Xn i) v F (η*r i) → Knock b (n i) (m i) p k d ℓ t (η*r i) a C s v F:=by
    let J(i):=n i+1; have hJ: Tendsto J l atTop:= tendsto_atTop_mono' _ (Eventually.of_forall (fun i=>le_add_of_nonneg_right (b:=1) (by omega : 0≤ (1:ℕ)))) hn.grows
    let T:= fun i=> 2*(a+2)*(C.S.a (Xn i)); have hT:Tendsto T l (𝓝 0):=by simpa only[T,J,comp_apply,mul_zero] using (((S!).shrinks.comp hJ).const_mul (2*(a+2)))
    have hT':Tendsto (fun i=>(C.path.levels.budget i).B) atTop atTop:= Work.E01.radiusB_tendsto.comp (hat_rate _ hG)
    filter_upwards [hn.grows.eventually_ge_atTop b,hN,hT.eventually (gt_mem_nhds ((S!).radius_pos 0)),family_fills hG hm hR hB he,hJ.eventually (hT'.eventually_ge_atTop t),hJ.eventually hw,(C.path.levels.fits.deep.comp hJ).eventually_ge_atTop (Fintype.card (Color V × Motion))] with i hi hx hP he' h_K hv h₁ p v F hV h_F hΘ
    have hp':2*(a+2)*(C.S.a (Xn i)) < C.S.radius p:=by
       refine lt_of_lt_of_le (show T i<C.S.radius 0 from hP) ?_; unfold Schedule.radius; apply div_le_div_of_nonneg_right _ (by norm_num); exact_mod_cast (S!).period_strict.monotone (Nat.zero_le p)
    let B₀:= (Z! (Xn i)).B
    refine ⟨hi,hx,hV,?_,hp',he',(le_trans (show t ≤ B₀ from h_K) ?_),h_F,hΘ,h₁,hv,hg,hy⟩; swap
    · have hx:B₀≤ B₀^2:=(pow_one _).symm.trans_le (pow_le_pow_right₀ (Z! _|>.B_pos) (by norm_num)); change B₀≤ 1024*B₀^2; omega
    intro j; let k:= Xn i; let z:= v j; let p':= Lattice.wrap (C.side k p) z
    have hv':lift p'=v j:=within_phys (n:=k) _ (lt_of_le_of_lt (hV j) (by let hu:= b! k; have hw:0<hu:= (S!|>.a_pos _); linarith only [hp',mul_nonneg hp hw.le,hw]))
    have hb := (Ribbons.normC C k p p').1; rw [Schedule.place,hv'] at hb
    have hu := (S!).a_pos k; have htV : (separation p' 0:ℝ) ≤ a := le_of_mul_le_mul_left (le_trans hb ((hV _).trans_eq (mul_comm ..))) hu
    exact_mod_cast htV.trans hk
omit hn hN hR hm hG hB
end
-- Schedule demand packaging plus fallback permits.Pin by waiting older apertures
include hG Y hC
lemma reserves (hL: UV.Lacquer C D) : ∃ B:ℕ→ℕ→ℝ,∀ d t k:ℕ,∀ᶠ b in atTop,
    k ≤ b ∧ Pin C b d ∧ (∀ i,b ≤ i→ Pin C i d) ∧ d+3 ≤ (λ₀).J b ∧ Stock.Tabs.opens C.path.levels (bumper (2*t)) k b ∧ Awake D B b d:=by
    obtain ⟨B,hB⟩:= held hL; refine ⟨B,fun d t k=> ?_⟩; obtain ⟨v,hv⟩:= eventually_atTop.mp (feathery hC hG Y d)
    let u:= bumper (2*t); let l:=Stock.Tabs.chosen Θ u Y.tabs k
    have hw:=Stock.Tabs.opened Θ u Y.tabs k
    filter_upwards [hB d,eventually_ge_atTop v,eventually_ge_atTop l, (Θ|>.fits.deep.eventually_ge_atTop (d+3))] with b hb hx hp hJ using ⟨hw.1.trans hp,hv b hx,fun i hi=> hv _ (hx.trans hi),hJ,Stock.Tabs.open_later Θ u Y.tabs hw hp (by unfold u bumper; positivity),hb⟩
end YM.RG05Readout.Halls
