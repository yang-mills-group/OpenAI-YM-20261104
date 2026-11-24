import YM.OPE.Compatible.Glades.Badge
/-! Invoice in log compact shape
Choose w for final ticket big enough for multiplicands but still within margin(s).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open Push Marker Local Extra.Histories Extra.Trajectories MeasureTheory Extra.Multi Finset Bid
open scoped Topology Classical
variable {G:Gauge}{C:Family G}{J k j p d:ℕ}{a b:ℝ}
-- k=fix, j=ready
set_option quotPrecheck false

local notation "μ"=> near C.path.levels
local notation "δ"=> renal C.path.levels j
local notation "c"=> C.path.levels.params j |>.columns
-- auxiliary estimates

def owed (C:Family G)(a:ℝ)(d j:ℕ) :=4*(1+(C.path.levels.params j).columns)*(2*(C.S.a (j+1)^d*(β C (j+1)*(4*(1/a)))))
def badge_fee (C:Family G)(a:ℝ)(j:ℕ):= a/(16*β C (j+1))
-- entire test-array quota level k, root alignment fixed
-- ensuring march ≤ account and bequeath
def rebate (C:Family G)(a:ℝ)(d k j:ℕ):=
    min (fly C.path.levels d k/(64*(1+(C.path.levels.params j).columns)*‖alto C.path k d‖*owed C a d j))
        ((renal C.path.levels j*badge_fee C a j)/((C.S.a j/C.S.a k)^d)) -- ζ ratio paid by schedule for d. seeing yields `(a_? etc ζ)`.
variable (hp:0<a)(A:Allot C)(hP:C.ref d ≤ k)(hq:k ≤ j)
include hp
lemma badge_pos : 0 < badge_fee C a j:= div_pos hp (mul_pos (by norm_num) (β_pos ..))
lemma owed_pos : 0<owed C a d j:=by
    unfold owed; exact mul_pos (mul_pos (by norm_num) (zero_lt_one.trans_le (show 1 ≤ 1+c from by have h:1≤c:= (C.path.levels.params j).columns_ge;linarith only [h]))) (mul_pos zero_lt_two (mul_pos (pow_pos (C.S.a_pos _) _) (mul_pos (β_pos ..) (by positivity))))
omit hp

private lemma hknows (C:Family G)(a:ℝ)(ha:0<a)(d k j:ℕ) :0 <64*(1+(C.path.levels.params j).columns)*‖alto C.path k d‖*owed C a d j:=by
    rw [alto_norm]; have hh:= C.path.S.a_pos k; have ht:= owed_pos (C:=C) (d:=d) (j:=j) ha; have h':0<1+(C.path.levels.params j).columns:= by linarith only [(C.path.levels.params j).columns_ge]
    positivity
include hp A hP hq
set_option linter.unusedSectionVars true
lemma rebate_positive : 0< rebate C a d k j:=lt_min (div_pos (A.buy.system.grows _ _ hP) (hknows C a hp d k j)) (div_pos (mul_pos (A.buy.system.costs.stay.water _ ((Nat.zero_le k).trans hq)|>.2) (badge_pos hp)) (pow_pos (div_pos (C.S.a_pos _) (C.S.a_pos _)) _))
lemma setting_value (hg:G.Simple):
    march (fun _:Unit=>rebate C a d k j) μ k j () ≤ δ * badge_fee C a j∧
    32*(1+(C.path.levels.params j).columns)*rebate C a d k j * ‖alto C.path k d‖ * (owed C a d j/gainChart C.path j k) ≤ fly C.path.levels d k /2 :=by
    let w:= rebate C a d k j; have hw:= (show 0<w from rebate_positive hp A hP hq); let t:= C.S.a j/C.S.a k; have he:0<t:= div_pos (C.S.a_pos _) (C.S.a_pos _); have he':t ≤ 1:= (div_le_one (C.S.a_pos _)).2 (C.S.strictAnti.antitone hq)
    let u:= (C.path.levels.params j).columns; let K:= owed C a d j; have hK:0 < K:= owed_pos hp; let y:=fly C.path.levels d; have hy:0< y k:= A.buy.system.grows _ _ hP
    constructor
    · apply le_trans (seeing (b:=w) C d A.buy.system hw j k hP hq); have h1 : y j ≤ y k:=fly_le hg d k j hq
      apply le_trans ?_ ((le_div_iff₀ (pow_pos he d)).1 (show w ≤ _ from min_le_right ..))
      exact (mul_le_of_le_one_right (mul_nonneg hw.le (pow_nonneg he.le _)) ((div_le_one hy).2 h1)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one he.le he' d.le_succ) hw.le) -- 
    let v:=1+u; let x':= gainChart C.path j k; have ht':1≤u:=(C.path.levels.params j).columns_ge
    have hu:1≤x':= Real.one_le_exp (mul_nonneg (by norm_num) (sub_nonneg.mpr ((scale_mono C.S).monotone hq)))
    let z:= ‖alto C.path k d‖
    apply le_trans (mul_le_mul_of_nonneg_left (show K/x'≤K from div_le_self hK.le hu) (show 0≤32*v*w*z from by have hh:0 < v:=add_pos_of_pos_of_nonneg one_pos (zero_le_one.trans ht'); unfold z; positivity))
    have hx := (le_div_iff₀ (hknows C a hp d k j)).mp (show w ≤ y k/(64*(1+u)*z*K) from min_le_left ..)
    change 32*v*w*z*K ≤ _; change w*(64*v*z*K) ≤ _ at hx; change _ ≤ y k/2; linarith only [hx]
end YM.OPE.Allot
