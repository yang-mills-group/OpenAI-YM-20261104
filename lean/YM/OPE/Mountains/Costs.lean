import YM.OPE.Mountains.Mural
import YM.OPE.Trees.Repairs
import YM.OPE.Screens.Takes
/-!
# Layer and actual radius price
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Finset OPE.Log Mountain Trunk
open scoped Classical Topology BigOperators ContDiff
set_option quotPrecheck false
variable {G:Gauge}{L:Register G}
variable {I J:Type}[Fintype I] {s:Arboreal I} {φ:Ultrafilter J} {t:I→ℝ} {x:J→I→ E4}{R:J→I→ℝ}{M δ:ℝ}{i j k o u:I} {a b : Finset I} (p:I→ L.Token) (d:ℕ)

def rent (s:Arboreal I)(p:I→L.Token)(r:I→ℝ)(b:Finset I): ℝ:=∏ i∈b,r (s.parent i) ^ (p i).1
def fee (s:Arboreal I)(p:I→ L.Token)(r:I→ℝ)(b: Finset I)(i:I)(d:ℕ): ℝ:= s.rent p r b / (r i)^d

variable {R': I→ℝ} (hg: s.Graduated R')
lemma Graduated.rent_pos (hg: s.Graduated R') : 0<s.rent p R' b := prod_pos (fun j _=>pow_pos (hg.allowed _ (s.inward j)) _)
lemma Graduated.fee_pos (hg: s.Graduated R')(hi:i∈ s.zones):0<s.fee p R' b i d:= div_pos (hg.rent_pos p) (pow_pos (hg.allowed _ hi) _)
lemma Graduated.wallet (hg:s.Graduated R') (ht:s.Active a)(hi:i∈s.middle a) (t:L.Token):
    s.fee p R' (s.live a) s.root d = s.fee p R' (s.inputs a i) i t.fst * s.fee (update p i t) R' (s.live (s.redact a i)) s.root d * s.ratioAt R' i^t.fst:=by
    let q:= update p i t; let f:=s.inputs a i; let g:=s.external a i; have hf : s.rent p R' (s.live a)= s.rent p R' f * s.rent p R' g:=by
       unfold rent
       conv_lhs=> arg 1; rw [← s.divide a i]; -- inspect
       exact prod_union (s.divided ..)
    have he : s.rent q R' (s.live (s.redact a i)) = R' (s.parent i)^t.fst * s.rent p R' g:=by
       rw [pruned ht hi]; unfold rent q; rw [prod_insert (no_shadow s i a), update_self]; apply congr_arg; refine prod_congr rfl fun j hj=>?_ ; rw [Function.update_of_ne (live_other (mem_erase.mp hi).2 (exterior_mem.mp hj).1)]
    have hu:0<R' s.root:= hg.allowed _ s.initial; have hp:=hg.allowed _ (s.inward i); have hv:=hg.allowed _ (ht.included (mem_erase.mp hi).2)
    change _ = _ * s.fee q R' _ _ d * _; unfold fee ratioAt; rw [hf,he,div_pow]; field_simp; exact mul_comm .. 

local notation "T'"=> (fun i=>s.fullLife (R i))
variable (h:s.Coterie (φ:Filter J) t M δ x R)
include h
lemma fee_is (b:Finset I) (hi:i∈s.zones) : RateIs (φ:Filter J) T' (fun j=> s.fee p (R j) b i d) (d*t i-s.onset t p b) :=by
    let f (i:I):= fun j:J=> R j (s.parent i)^(p i).1; have he(j:I):RateIs (φ:Filter J) T' (f j) (-((p j).1*t (s.parent j))):= ((h.tracked.rates (s.parent j) (s.inward j)).power _).swap (by ring); let V:= R
    apply (((RateIs.prod (S:=b) (fun j _=>he j) h.time)).div ((h.tracked.rates _ hi).power d)).swap; unfold onset; rw [Finset.sum_neg_distrib]; ring
lemma savings (hi:i∈s.zones) : Wallet (φ: Filter J) T' (fun j=>s.ratioAt (R j) i) := (Wallet.const h.time (1:ℝ)).of_le' ((ratio_rate h.tracked hi).pos) (h.space.mono (fun j hj=> (div_le_one (hj.sizes.allowed _ (s.inward i))).2 (hj.sizes.coarser _ hi)))
omit h
-- composing powers for expansions (match through any leap, including
-- successive same-layer layers)
lemma joinUp (x y: ℂ) (a b : ℝ): (a • x)*(b • y) = (a*b) • (x*y):= by rw [smul_mul_assoc, mul_smul_comm, mul_smul]
lemma multiply_cash {F F':J→ℂ} {W:J→ℝ} (h:s.Coterie (φ:Filter J) t M δ x R)(ht:s.Active a)(hi:i∈ s.middle a)(ξ:L.Token)
    (hF:Wallet (φ:Filter J) T' (fun j=>s.fee p (R j) (s.inputs a i) i ξ.fst • F j))
    (hF':Wallet (φ:Filter J) T' (fun j=> (s.fee (update p i ξ) (R j) (s.live (s.redact a i)) s.root d* W j) • F' j)): Wallet (φ:Filter J) T' (fun j=> (s.fee p (R j) (s.live a) s.root d* W j) • (F j * F' j)):=by
    apply (((Arboreal.savings h (ht.included (mem_erase.mp hi).2)).pow h.time ξ.fst).smul (hF.mul hF')).congr; filter_upwards [h.space] with j hj; rw [joinUp,← mul_smul,hj.sizes.wallet p d ht hi ξ]; congr 1; ring
namespace Portrait
include h
variable (V:Portrait s φ R o)
variable (r : b) (hp:∀ i∈ b,s.Anc o (s.parent i))
local notation "I'"=> (↑b:Type)
local notation "Q"=> frame h V r hp
lemma tag (hi:o∈ s.zones) : ValueStamp (φ: Filter J) T' (fun i=> s.fee p (R i) b o d / (Payments.priceSet Q univ (crop p b) (V.top i) / (V.top i 0)^ d)) := by
    let f(j:I') (i:J):= (R i (s.parent j.val)/V.top i ((Q).age j))^(p j.val).1; have hT:=h.time; let z(j:I')(k:ℕ):= k* (p j.val).fst; have he : ValueStamp (φ: Filter J) T' (fun i=> s.rent p (R i) b / Payments.priceSet Q univ (crop p b) (V.top i)):=by
       have hv (j:I'):ValueStamp (φ: Filter J) T' (f j):= (led h V (tower_at.mpr ⟨s.inward _ , hp _ j.property⟩)).pow h.time _
       apply (ValueStamp.prod (s:=univ) h.time (fun j _=> hv j)).congr; filter_upwards with i
       unfold f Payments.priceSet rent; simp_rw [div_pow]; rw [prod_div_distrib, prod_coe_sort (s:=b) (fun j=> R i (s.parent j)^(p j).1)] -- name
    have he' := (led h V (i:=o) (tower_at.mpr ⟨hi,Anc.same ..⟩)); rw [Portrait.mark h V hi] at he'
    apply (he.div (he'.pow h.time d)).congr; filter_upwards with i; unfold fee; rw [div_pow]; ring_nf
lemma value (i:I)(hi:i∈s.zones)(hz:s.Anc o (s.parent i)): ValueStamp (φ:Filter J) T' (fun j=> (((R j (s.parent i))/(R j i))^d)/Payments.fuel (V.top j) (V.hue i) (V.hue (s.parent i)) d):=by
    apply (((led h V (tower_at.mpr ⟨s.inward _,hz⟩)).div (led h V (tower_at.mpr ⟨hi,hz.joins (Anc.step s i)⟩))).pow h.time d).congr; filter_upwards with j; unfold Payments.fuel; rw [← div_pow]; congr 1; simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]; ring
lemma positive : ∀ᶠ i in φ,0< Payments.priceSet Q univ (crop p b) (V.top i) / (V.top i 0)^d:=by
    filter_upwards [(V.schedule.ahead (Nat.zero_le V.limit)).pos,eventually_all.mpr (fun i:I'=> (V.schedule.ahead ((Q).bounded i)).pos)] with i hi hp'; exact div_pos (prod_pos (fun i _=> pow_pos (hp' i) _)) (pow_pos hi _)
end Portrait
end YM.OPE.Arboreal
