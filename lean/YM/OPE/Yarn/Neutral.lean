import YM.OPE.Yarn.Custom
import YM.OPE.Yarn.Expense
/-!
# Fitted at this declared moving stop and at any fixed stop demanded of
it separately. Works following primed() and the fixed transition.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{G:Gauge}{n: Side} {C:Family G} {k j z l m p N d b:ℕ}
variable {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ)
set_option quotPrecheck false
local notation "P" => C.path
local notation "T" => C.path.levels
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
local notation "ψ" => waybill C.path.levels
local notation "R" => C.path.rep N p
local notation "h*" => C.path.levels.clock.hatBeta
local notation "V" => Site (C.side m p)
variable {F:I→ Config G (C.side N p)→ℂ}{o:I→ ∀ i:ℕ, Site (C.side i p)}{w:I→ℝ}{u:I→Pod}{v:J→Pod} {d₀:Finset I}{Y:I→∀ i:ℕ,Lamp G (C.side i p)}{X:I→Lamp G (C.side k p)}
def wax (C:Family G)(b l k:ℕ):= license C.path (renal C.path.levels) b l k*near C.path.levels k
def submit (C:Family G)(d b l j k:ℕ)(x:ℝ):= bid C d j k x * wax C b l k
variable {P' : Coefficient (C.labels.level d) (C.side k p)} {x:ℝ}
local notation "U" => submit C d b l
local notation "E₀"=> Loom.ebb C d k x
include H
variable (ht:C.ref d ≤ j)(hk:j≤k)(hz:C.ref 0 ≤ k)(hx:0<x)(hb:0 < b)
include ht hk hz hx hb
lemma fitted (l:ℕ) : 0<submit C d b l j k x ∧ stair η (submit C d b l j k x) j k ≤ wax C b l k*tarred C k x ∧
     32*(1+(C.path.levels.params k).columns)*submit C d b l j k x * ‖alto C.path j d‖*(ebb C d k x/gainChart C.path k j) ≤ ζ d j/2:=by
    let z:= wax C b l k; obtain ⟨he,hK,hV⟩:= Loom.prices (C:=C) H.cuts d j ht hx hk; let w:=bid C d j k x; have hδ:δ k ≤1:= (H.mantle hz).funs.2; have hη: 0<η k:=(H.brine k).water _ le_rfl |>.1; have hζ:= ebb_pos (C:=C) d (m:=k) hx; let t':= tarred C k x; have ht': 0<t':= div_pos hx (mul_pos (by norm_num) (by exact zero_lt_one.trans ((T).fits.delayed _))); have hu':1≤(C.path.levels.params k).columns:=(C.path.levels.params k).columns_ge
    have hu:0<z:= mul_pos (license_pos b l (H.mantle hz).funs.1 hb) hη; have h: z ≤ 1:= by
       apply mul_le_one₀ ((unit_license b l (H.mantle hz) hb (T|>.budget k|>.exponent_pos.le)).trans hδ) hη.le ((inv_le_one₀ (zero_lt_one.trans ((T).fits.delayed (k+1)))).mpr ((T).fits.delayed _|>.le))
    refine ⟨mul_pos he hu,?_ ,?_⟩
    · change stair η (w*z) j k≤ z*t'; rw [show stair η (w*z) j k=z*stair η w j k from (by rw [stair_eq η (w*z), stair_eq η w]; ring)]; exact mul_le_mul_of_nonneg_left (le_trans hK (mul_le_of_le_one_left ht'.le hδ)) hu.le
    exact le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right he.le h) (by positivity)) (norm_nonneg _)) (div_nonneg hζ.le (Real.exp_nonneg _))) hV
lemma assemble (l:ℕ){Y:Lamp G (C.side k p)} (hN:k≤N)(hI: Ignite C.path N p k C.params (C.localSection d) P' (earPay C d k x) 0 Y): ∃ B:Album C N k p d, Chant W D ζ ψ η P' (ebb C d k x) B hN:=by
    have he:= hI.power; have hE:= fitted H ht hk hz hx hb l
    have hq:0<earPay C d k x:= by unfold earPay; have hz:= C.S.a_pos (k+1); have hs:= (T).fits.delayed (k+1); positivity
    exact Patrol.chant H.seed H.cuts.system P' ht hk hN hI.fuel he.1 (le_trans (add_le_add_left he.2 _) (by ring_nf; exact le_rfl : _+_≤2*earPay C d k x)) (mul_pos zero_lt_two hq) le_rfl hE.1 hE.2.2
variable {B:Album C N k p d}
    (i:I){hm:m≤k}{hn:k<N}(hB:Chant W D (fly C.path.levels) (waybill C.path.levels) (near C.path.levels) P' (ebb C d k x) B hn.le)
    (hI:Ignite C.path N p k C.params (C.localSection d) P' (earPay C d k x) 0 (X i))
    (ho:o i=fun i=>(0:Site (C.side i p)))(hR:GridApprox.room C.path.levels m k (lensScope C d))
    (hh: wax C b l k*tarred C k x ≤ pocket C (u i) k 1 (w i))
include hB hI ho hR hh
local notation "M"=> center C.S p (hm.trans hn.le) 0
set_option maxHeartbeats 200000 in
lemma fetching (hr:CrewBook C N p m k D hm hn.le F d₀ o u w Y X)(hf:Interior ((center C.S p (hm.trans hn.le) 0).chamber 0) (F i)) (hC:∀ (b': C.label d), Interior ((center C.S p (hm.trans hn.le) 0).chamber 0) (C.O N p b' 0))
    (hp:Stock.Tabs.opens C.path.levels 1 m j) (hs:j<k): Next.UVStress.quota C d k N p B.legacy ≤ 2*E₀ ∧ (M).rootTest (C.beta N p) (F i-C.O N p B.legacy 0) ≤ 2*(stakes C m j / (U j k x)):=by
    obtain ⟨Q,hQ⟩:=hr.ready; have hE:= fitted H ht hk hz hx hb l
    exact Wagon.capture H.seed H.cuts.system hn hQ H.cuts.tabs hp ht hs hR hC _ (congr_fun ho _) hf hB hI (Loom.ebb_pos (C:=C) d hx) hE.1 hE.2.2 (hE.2.1.trans hh)
-- protect until sanctuary j from here. `score`. bQuest enters (used externally Grip).
set_option maxHeartbeats 200000 in
lemma locker (hr:CrewBook C N p m k D hm hn.le F ∅ o u w Y X) : ∃ S,CrewBook C N p m k D hm hn.le (Function.update F i (F i+GridApprox.backTo C.path N p hn.le B.body)) {i} o (Function.update u i (some j)) (Function.update w i (U j k x)) (Function.update Y i S) (Function.update X i (S k)) := by
    have hE:= fitted H ht hk hz hx hb l
    obtain ⟨S,hS,hΩ⟩:= score_mark H.seed H.cuts.system hn.le ht hk hE.1 (ebb_pos d hx (C:=C)) (hB.window _ j ht hk hE.1 hE.2.2) hB (X i) hI
    exact ⟨S,CrewBook.additive H i hr hE.1 (ho.symm ▸ hS) hΩ.1 hΩ.2 (hE.2.1.trans hh) (YM.ProofPorts.GridRealModelEstimates.interior_sum _ _ (fun i _=> (visible C N k p d _ H.seed hn.le).scale _)) hR ⟩
end YM.OPE.Yarn

