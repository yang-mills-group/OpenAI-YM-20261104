import YM.Frontier6.Multi.Storage.Roadbed
import YM.Frontier6.Multi.Bonds.Vel
import YM.Frontier6.Pair.FusionCost

/-! Scene threading across cell seams via root anchors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Canopies.Doors
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory Matrix
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Next.Rank Next.Rank.Station Cells
open Ribbons
open scoped Topology BigOperators Classical
variable {G:Gauge}{O:Type}[DecidableEq O][Fintype O]
variable (C:Family G)(J j p:ℕ)
variable (L : O → Site (C.side j p))
set_option quotPrecheck false
local notation "Q"=> hands C p J
local notation "V"=> Site (C.side J p)
local notation "E"=> Mix.camp C p J

def placements (i:ℕ) (x:Live (Site (C.side J p)) O) : Site (C.side i p):= bites C J j p (L x.2) i (x.1,true)
local notation "b"=> placements C J j p L
variable {i m k:ℕ}
lemma shaped (hi:J ≤ i) : Shaped (0: Site (C.side J p)) (Q) (E i) (placements C J j p L i):=fun j _ k=>bit C J _ p i (L k) hi j true
lemma transit (hk:J≤j) (N:ℕ): Migrating C.path j p N (placements C J j p L):= ⟨fun i hi he=>funext (fun x=>congr_fun ((retina C J j p N (L x.2) hk).mare i hi he) (x.1,true))⟩
lemma returns (hm:J ≤ m)(hi:m ≤ i)(hx:i≤j): (C.S.toDepth hi p).parent ∘ b i=b m:=funext fun x=> congr_fun (bitesParent C J j p m (L x.2) hm hi hx) (x.1,true)
lemma sent (hz:J ≤ i)(he:i<j): (C.path.levels.clock.op i p).ratio.parent ∘ b (i+1)=b i:=by
    rw [show (C.path.levels.clock.op i p).ratio=C.S.toDepth i.le_succ p from ratio_same ..]
    exact returns C J j p L hz i.le_succ he
lemma meet_base (hj:J≤j) : ∀ i:O,b j (0,i)=L i:=fun i=> (biteT C _ _ _ _ _ hj).trans (same ..)
lemma summit (hj:J≤j)(hv:Pairwise (fun i k=> (C.path.levels.budget j).B^2 ≤ separation (L i) (L k))) : Daylight (0:V) (placements C J j p L j) ((C.path.levels.budget j).B):=by intro i k h; rw [meet_base,meet_base]; exact hv h; all_goals assumption
local notation "P"=> C.path.levels.budget
local notation "R"=> C.path.levels
lemma herd (hm:J ≤ m)(hh:m ≤ j)(hs:∀ i:O,loops C j p (L i) m=0): ∀ (x:Live V O), b m x=E m x.1:=by intro x; unfold placements bites; rw [if_pos rfl,hs]; simp [affine]
lemma fleet (hm:J ≤ m)(hk:m ≤ j)(hs:∀ i:O,loops C j p (L i) m=0) (ht:(C.path.levels.budget m).B^2+1 ≤ (C.S.toDepth hm p).count.val) {δ φ:ℕ→ℝ}(h:Brine C.path m δ φ) (hf:m ≤ i)(he:i≤j): Between (placements C J j p L i) ((C.path.levels.budget i).B):=by
    intro s u hΔ
    have hT : (P m).B^2+1 ≤ separation (b m s) (b m u):=by
        rw [herd C J j p L hm hk hs,herd C J j p L hm hk hs]; apply ht.trans; simp_rw [elev C J p m hm, Station.both]; exact Nat.le_mul_of_pos_right _ (separation_pos _ _ hΔ)
    have hh:=(returns C J j p L hm hf he)
    let T:= C.S.toDepth hf p; let L':=T.count.val; have hx(x): 2*separation (b i x) (T.embed (b m x))< L':=by rw [← hh]; exact midway T (C.S.toDepth_odd hf p) _
    have ht:L'*((P m).B^2+1) ≤ separation (T.embed (b m s)) (T.embed (b m u)):=by rw [Station.both]; exact Nat.mul_le_mul_left _ hT
    have hh₁:= separation_triangle (T.embed (b m s)) (b i s) (T.embed (b m u)); have hh₂:=separation_triangle (b i s) (b i u) (T.embed (b m u)); rw [separation_comm (T.embed (b m s)) (b i s)] at hh₁ -- which?
    have he':(P i).B^2 ≤ L'*(P m).B^2:=gap_comp C p m i h hf; have hh₃:=hx s; have hh₄:=hx u; rw [mul_add,mul_one] at ht; omega
section
variable {δ φ ψ ζ:ℕ→ℝ}{u:ℕ→ℕ→ℝ} {W:Bid.Worth}{r:ℕ→ℕ}{D:∀ N p i,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (h:Scrim C W ζ ψ φ δ u r D) {χ:ℕ→ℝ}{d:ℕ}{ε:ℝ}
variable (h' : WaresAll C (δ:=δ) (r:=r) (μ:=D) (C.ref d) d χ δ (PhysicalNext.Repeat.Legato.bling C.path.levels)) {N:ℕ}
lemma allBrine (h:Scrim C W ζ ψ φ δ u r D)(k:ℕ) : Brine C.path k δ φ:=⟨fun i _=> h.costs.stay.water _ (Nat.zero_le i),fun i _=> h.costs.stay.mint _ (Nat.zero_le i),fun i _=> h.costs.stay.split _ (Nat.zero_le i),fun i _=>h.costs.stay.support _ (Nat.zero_le i)⟩
include h h'
lemma route (hm:J ≤ m)(hh:m+1<j)(hN:j<N)(hk:C.ref d ≤ m)(hs:∀ i:O,loops C j p (L i) (m+1)=0) (ht:(C.path.levels.budget (m+1)).B^2+1 ≤ (C.S.toDepth (hm.trans m.le_succ) p).count.val)(he:0 < ε)(hy:ε ≤ 1)(hX:∀ i:ℕ,m < i→ i<j→ ε ≤ restoreRate C.path.levels δ i)(hA:Fintype.card O ≤ r m): Travel C.path δ r D χ 0 (Q) (Equiv.swap 0) E (placements C J j p L) m j (C.ref d) ε N:=by
    let H:=C.path.levels; let v:= C.ref d; have hr(i:ℕ)(hi:m ≤ i)(he:i<j):φ i ≤1:=by
       obtain ⟨-,hf,-⟩:= (h.costs.heights d m N p hk (by omega : m ≤N)).choose_spec
       exact hf.level i hi -- inspect
    refine ⟨hk,fun i hv _ hn=> (h'.brings i (hk.trans hv.le) N p hn).1,fun i hi he' => ?_,fun i hi _=>h'.bars i (hk.trans hi.le),⟨he,hy,hX⟩,fun i hi _=> funext fun x=> Work.I03.camp_step C p (hm.trans hi) x, fun i hi hj=> sent C J j p L (hm.trans hi.le) hj,fun i hi hj=> shaped C J j p L (hm.trans hi.le),fun i hf he'=>fleet C J j p L (hm.trans m.le_succ) hh.le hs ht (allBrine C h (m+1)) hf he', fun i h=>Equiv.swap_apply_left ..,fun i hi=>hA.trans (h.costs.mom hi)⟩
    have hE :0 < δ i:=(allBrine C h m|>.water i hi.le).2
    exact ⟨(allBrine C h m|>.mint i hi.le).trans (mul_le_mul_of_nonneg_right (by exact mul_le_of_le_one_right hE.le (hr i hi.le he')) (Real.exp_pos _|>.le : 0≤ mintK _)), (allBrine C h m).support i hi.le⟩
end
end YM.MergeProof.Canopies.Doors
