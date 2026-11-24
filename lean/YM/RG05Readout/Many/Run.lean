import YM.RG05Readout.Many.Reopen
/-!
# Ancestor reading before actual b-capture

Output certified for any true density path/presentation of the specified
sources at top, not simply one restricted launch. Test shape separated
at admitted m; distinct copies uniformly. Restores
complete simultaneous choices permitted at that b base. Widths external
exhibitable from readiness (`pulseFee`, supply).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {n m p N d:ℕ}{W:Type}[DecidableEq W][Fintype W]
    {D:Address.Rail C} {w:Worth}{r:ℕ→ℕ} {k g:ℕ}
set_option quotPrecheck false
local notation "Z₀"=> C.path.levels
local notation "t₁"=> C.path.levels.budget
local notation "K"=> C.path.levels.clock
local notation "Y"=> C.path.rep N p
local notation "L!"=> C.path.levels.clock.op
local notation "ζ"=> Legato.Bandage.fly C.path.levels
local notation "λ₁"=> far C.path.levels
variable (o:W→Site (C.side n p)) (E:W→Motion) (s:W→ℕ) (I:∀ i:ℕ, ManyStem C o i → Body)
local notation "V_"=> ManyStem C o
local notation "A"=> Mine.tree o E
local notation "Λ"=>(A).labelY
local notation "Φ"=>(A).narrows
local notation "H!"=> Mine.ward o E
local notation "r₀"=>(A).supportX
variable (h:C.Makes) (L:OPE.Package C w r D) (hw:Storage C D)
variable {v:(i:W)→ℕ→Palette C (s i)} {T:Pens C p W} {f q:ℕ→ℝ}{B:ℕ→ℕ→ℝ}
local notation "w₀"=> west C q f k
local notation "λ₀"=> fun i : V_ N=> stepUp ((A).motion (Λ N i)) (r₀ N i) (entrance C (s (Λ N i)) N p (v (Λ N i) N) 0 (I N i))
local notation "ι"=> shadow A s I
local notation "M₀"=> apron C.path.levels
local notation "Y!"=> fun k i=> if i=k then (t₁ i).supportExponent-4 else (t₁ i).supportExponent

-- m proximity rule defined in terms of the prepared tests. Assume hp≥ except blackout any pair.
def Choices (i:ℕ)(H:Census (ManyStem C o i)):Prop:= ∀ h:H.Mode,2≤h.val.card → ∀ v∈h.val,∀ w∈h.val,v ≠ w → ((C.path.levels.budget i).B)^2+1 ≤ separation ((Mine.tree o E).supportX i v) ((Mine.tree o E).supportX i w)
def barren (B:Census W)(m:ℕ): Census (ManyStem C o m) where
    choices:= (H! B m).choices.filter fun p=> (p:Set _).Pairwise (fun i j=> ((t₁ m).B)^2+1 ≤ separation (r₀ m i) (r₀ m j))
    blank:=by simp [(H! B m).blank]
    solo:=by intro i; simp [(H! B m).solo]
    down {x} hx y hy:=by simp only [Finset.mem_filter] at hx; exact Finset.mem_filter.mpr ⟨(H! B m).down hx.1 y hy,hx.2.mono hy⟩
lemma barraged (B:Census W):Choices o E m (barren o E B m):=fun h _ _ hi _ hj hij=> ((Finset.mem_filter.mp h.property).2) hi hj hij
def Clearance (B:Census W)(m:ℕ) : Prop:= ∀ h:(Mine.ward o E B m).Mode, Disjoint (shadow (Mine.tree o E) s I m) (h.val:Set _) → (h.val:Set _).Pairwise (fun i j=> ((t₁ m).B)^2+1 ≤ separation (r₀ m i) (r₀ m j))
open Mine
lemma masts_block (hp:n ≤ m) (B:Census W) (hx: Clearance o E s I B m) : ∀ i:(H! B m).Mode,i.val ∉ (masts o E hp (barren o E B m) m).choices → ¬Disjoint (ι m) (i.val:Set _):=by
    intro i h he; apply h; have hh:i.val ∈ (barren o E B m).choices:= Finset.mem_filter.mpr ⟨i.property,hx i he⟩
    unfold Mine.masts; rw [dif_pos le_rfl]; apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _,?_⟩; rw [show shelter o hp (le_refl _) = id from funext fun j=> vanishDepth o j hp]; exact ⟨by simpa using hh,Set.injOn_id _⟩
-- Actual even in active selection at m. Width sacrifice for final m closing.
variable {Λ':Census W} {F:∀ i:ℕ, Config G (C.side i p)→Poly (Mine.ward o E Λ' i)}
include h hw L
set_option maxHeartbeats 700000 in
lemma anchored (hk:n ≤ m)(hm:m≤ N) (ht:Occupancy o ((K).J n)) (hc: Clearance o E s I Λ' m)
    (hf:∀ i, m ≤ i → i<N → f i ≤ f (i+1)) (hF:∀ i,n ≤ i→ i < m → f i ≤ f (i+1)*((C.path.levels.clock.hatBeta i)^(3*k+4))⁻¹)
    (he:Purse C f q n N d k) (hl:Lesson (D:=D) h s n N N p T B q v)
    (ho:∀ i≤ d,C.ref i≤N)(hS:∀ i,s i≤ d)(hW:∀ i:V_ n, Cap (s (Λ n i)+2) (I n i) 1)(hP:PreparedA A I n N le_rfl)
    (hx:∀ i≤ d,pricesTop ζ λ₁ N i ≤ (λ₁ N)*((C.path.levels.clock.hatBeta N)^k))
    (hY:F N=birth (H! Λ' N) (Y N) λ₀)(hr:Replay A s (H:=H! Λ') (le_refl n) N F N):∀ i:ℕ, n ≤ i →∀ hp:i≤ m,MenuBoard (R:=H! Λ' i) (Y i) (imprint h A I T i (hp.trans hm)) (F i) (r₀ i) (fun _:V_ i=>w₀ i) (Y! m i) 1:=by
    -- use bans predicate with warp.step.
    let R:= barren o E Λ' m; have hX:Choices o E m R:=barraged o E Λ'
    let B':=masts o E hk R; have hT : ∀ i:ℕ, n ≤ i→ Occupancy (((L! i p).ratio.parent) ∘ (r₀ (i+1))) (M₀ i)∧ Occupancy (r₀ (i+1)) (M₀ i):=fun i hi=>Mine.pays o E hi ht le_rfl
    have h₁:Toured A B' hk N f k:=⟨fun i hi _=> (hT _ (hk.trans hi)).1,fun i hi _=> (hT _ (hk.trans hi)).2,fun i hi hv=> .via (shelter_test o E hk hi R L.tabs hX) (hf i hi hv)⟩
    have h₂:Toured A (H! Λ') (le_refl n) m f k:=⟨fun i hi _=> (hT _ hi).1,fun i hi _=>(hT _ hi).2,fun i hi hv=> .straight (hF i hi hv)⟩
    have hN:Occupancy (r₀ N) (M₀ N):=by
       intro x; apply le_trans (keep_occ o E (hk.trans hm) ht x);
       have hN' : (K).J n ≤ (K).J (N+1)+2:= ((Z₀).fits.mono ((hk.trans hm).trans N.le_succ)).trans (Nat.le_add_right _ _); exact hN'.trans (Nat.le_mul_of_pos_right _ (pow_pos (C.S.block N).property _))
    obtain ⟨F',hh,hQ⟩:= reels_write A s hk hm (H:=B') (fun i hi hv=>dawnwide o E hk R hi) (birth (B' N) (Y N) λ₀) N
    have h':=regenerate A s I h L hw hk le_rfl hm he hl ho hS hW hP hQ hY hx hN h₁ hh hr (fun i hi=> masts_le o E hk R Λ' (Finset.filter_subset ..) hi) (masts_block o E s I hk Λ' hc)
    have hV : Lantern (p:=p) (b:=n) (D:=D) s h m N q T:= Lesson.lights s h (hl.revise s h (le_refl n) hm); apply session _ s I h hw (le_refl n) hm T (he.slice le_rfl hm) h₂ hV ?_ hS (fun k ht hh=> hP k ht (hh.trans_le hm)) hW ?_ h'
    · exact ⟨fun i hi hv=> hr.downhill (V:=ManyStem C o) i hi (hv.trans_le hm)⟩
    dsimp only; split; rfl; linarith
end YM.RG05Readout.Many
