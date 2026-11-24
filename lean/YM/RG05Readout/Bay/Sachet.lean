import YM.RG05Readout.Bay.Apse
import YM.RG05Readout.Harvest.Spec
import YM.UVExt.MatchedSlots
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Bay
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {j b k l:ℕ}{e Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "L"=> C.path.levels
local notation "χ"=> C.path.levels.clock.J
local notation "λ₀"=> C.S.toDepth
local notation "Α"=> C.S.a
local notation "Z"=> C.path.levels.budget
local notation "R0"=> C.path.rep N p
variable {V:Address.Sight C d p}{U:Address.Emblems C d}(hw:Awake D B b d)(ht:Spine D B h b p d N V U)
open Pulse Nuclear
open Extraction Extraction.Lease
open Push.RelayDifference UVExt UVExt.Slots

local notation "T!"=> Cells.center
local notation "α!"=> C.S.a
variable {w:Bid.Worth}{r:ℕ→ℕ}(Yc:OPE.Package C w r D)(Ys:Storage C D)(hG:G.Simple)

-- one-direction uniform after rebasing to any deeper measuring camp
include hw
lemma ongoing (hf:b ≤ j) : Awake D B j d:=⟨fun i hp=> (hw.post i hp).trans hf,fun i hp=>hw.cash i (hf.trans hp),fun p i N hp=>hw.toll p i N (hf.trans hp)⟩ -- include
omit hw
include Yc Ys hG
lemma enders (j m:ℕ):∃ (k v:ℕ),∃ hV:j ≤ v,v>m ∧ Warm C v (d+1) k ∧ 1 ≤ (L|>.clock.J v) ∧ Stock.Tabs.opens C.path.levels (bumper 0) j v∧ α! j/8 + α! v≤ α! j/4 ∧ ∀ p:ℕ,16*(1+0+Scope C d) ≤(C.S.toDepth hV p).count.val∧ α! j/8 + α! v*3 < C.S.radius p := by
    obtain ⟨k,h⟩:=warmups Ys Yc hG (d+1); let n:=Stock.Tabs.chosen (L) (bumper 0) Yc.tabs j; let a:=16*(1+0+Scope C d)
    have ht:∀ᶠ v:ℕ in atTop,∃ hV:j ≤ v,v>m ∧ Warm C v (d+1) k ∧ 1 ≤ (L|>.clock.J v) ∧ Stock.Tabs.opens C.path.levels (bumper 0) j v∧ α! j/8 + α! v≤ α! j/4 ∧ ∀ p:ℕ,a ≤(C.S.toDepth hV p).count.val∧ α! j/8 + α! v*3 < C.S.radius p:=by
       filter_upwards [h,eventually_ge_atTop j,eventually_ge_atTop n,eventually_gt_atTop m,L|>.fits.deep.eventually_ge_atTop 1,(show Tendsto (fun v:ℕ=> (a:ℝ)*C.S.a v) atTop (𝓝 0) by simpa only [mul_zero] using C.S.shrinks.const_mul (a:ℝ)).eventually (gt_mem_nhds (C.S.a_pos j)), C.S.shrinks.eventually (gt_mem_nhds (div_pos (C.S.a_pos j) (by norm_num : (0:ℝ)<8)))] with v hp hv hc he hr ht hs
       refine ⟨hv,he,hp,hr, Stock.Tabs.open_later (L) _ Yc.tabs (show Stock.Tabs.opens (L) (bumper 0) j n from Stock.Tabs.opened ..) hc (by unfold bumper; positivity),by linarith only [hs],fun p=>?_⟩
       constructor
       · let P:= C.S.toDepth hv p; have hx: (a:ℝ)≤ (P.count.val:ℝ):=le_of_mul_le_mul_left (show α! v*a ≤ α! v*P.count.val from (mul_comm ..).trans_le (ht.le.trans_eq (C.S.embeds_scale P).symm)) (C.S.a_pos _)
         exact_mod_cast hx
       obtain ⟨hq,hX⟩:= Harvest.radius_paid C j p; linarith only [hq,hX,hs]
    obtain ⟨v,hv⟩:=ht.exists; exact ⟨k,v,hv⟩
omit Yc Ys hG in
lemma progresses (T:Emblems C d)(hf:m≤b)(hp:b≤N)(M:Palette C d): Many.point T M m N= Many.point T (Many.point T M m b) b N:=by
    rw [weave_fine hf,weave_fine (hf.trans hp), weave_fine hp,sumwalk T hf hp]; rfl
include h hw
lemma training (j m:ℕ)(hy:b ≤ m)(Q:ℝ)(hq:0 < Q) : ∃ A:ℝ, 0 ≤ A ∧ ∀ᶠ N:ℕ in atTop, ∃ hp:j≤N,∀ (p:ℕ) (V:Address.Sight C d p)(U:Address.Emblems C d),Spine D B h b p d N V U → ∀ (M:Palette C d), size M ≤ Q → ∀ (q:Body), (∀ x∈ tsupport q.val, ‖x‖≤ C.S.a j/8) → Tall (E:=E4) q (d+2) 1 1 → Interior ((Cells.center C.S p hp 0).chamber 0) (fieldC C m N p d (Many.point U M m N) q) ∧ (Cells.center C.S p hp 0).rootTest (C.beta N p) (fieldC C m N p d (Many.point U M m N) q) ≤ A:=by
    obtain ⟨k,v,hV,he,hW,hP,hT,hξ,hz⟩:=enders (d:=d) Yc Ys hG j m
    let a:= total C Q (d+1) m (v+1); have ha:0<a:= totalpos hq _; have hw': 0 ≤ season C v d j k a B:=by
       exact (div_pos (Real.exp_pos _) (show 0< Many.envelope C (v+1) (d+1) k a v from mul_pos (rust_paid _).1 (grantw (totalpos ha _)))).le
    refine ⟨_, mul_nonneg (pow_nonneg (div_nonneg (C.S.a_pos m).le (C.S.a_pos v).le) d) (mul_nonneg (mul_nonneg (pow_nonneg (C.S.a_pos v).le 4) (pow_nonneg (div_nonneg (C.S.a_pos j).le (C.S.a_pos v).le) 4)) hw'),?_⟩
    filter_upwards [eventually_gt_atTop v] with N ht; refine ⟨by omega,fun p V U hU M hM q hx hv=>?_⟩
    have hr: size (Many.point U M m (v+1)) ≤ a:= head_cost hU hy (he.le.trans ht.le) (le_refl (d+1)) hM (by omega) ht -- hp order hy.trans he doesn't type he def Nat.lt
    rw [progresses U (Nat.le_trans he.le v.le_succ) ht M]; apply shallot h (ongoing hw (hy.trans he.le)) (Records.Spine.tail h V U hU (hy.trans he.le)) Yc Ys ht hV _ hr ha hW hP hT (v-1) (by omega) (hz p).1 hξ (hz p).2 q hx hv

omit Yc Ys hG hw h
lemma boarding (j:ℕ)(hV:b≤N)(hp:j≤b) (T:Tiling (C.side N p))(hs: T.side.val=Cells.span C.S (hp.trans hV) p){J:ℕ}(hJ:0<J)(ht:(3*J:ℕ)*α! b ≤ α! j) : 3*(Cells.span C.S hV p)≤T.side.val/J:=by
   apply (Nat.le_div_iff_mul_le hJ).2; apply (Nat.cast_le (α:=ℝ)).1; apply le_of_mul_le_mul_left _ (C.S.a_pos N); rw [hs, C.S.embeds_scale (C.S.toDepth (hp.trans hV) p)]; rw [← C.S.embeds_scale (C.S.toDepth hV p)] at ht; push_cast at *; linarith only [ht] -- span reducible?
include h
lemma material (j:ℕ)(hV:b≤ N)(hp:j ≤ b){V:Goods G (C.side N p)}{A:ℝ}(ht:Interior ((Cells.center C.S p hV 0).chamber 0) V)(hh:(Cells.center C.S p hV 0).rootTest (C.beta N p) V ≤ A) (T:Tiling (C.side N p))(hT: T.side.val=Cells.span C.S (hp.trans hV) p){J:ℕ}(hi:0<J)(ha:(3*J:ℕ)*α! b ≤ α! j) : UVExt.Slots.priceAt (T:=T) V J (C.beta N p) A:=by
    intro x hx b' s hs
    exact RelayDifference.offset hV T (C.beta N p) A (hT.symm ▸ Extraction.Around.inherits hp hV) (Slots.literal_oriented V b' s) (seamless h ..) (center_interior hV s hs b' 0 ht) (le_trans (center_price hV 0 V b' s hs ht _).le hh) (Lease.fewer T 0 (boarding j hV hp T hT hi ha) hx)
end YM.RG05Readout.Bay
