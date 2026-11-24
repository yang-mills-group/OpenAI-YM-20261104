import YM.RG05Readout.Many.Tour
/-!
# Reels across root regions

Propagate for general subinterval, cuts chosen literally. Sessions start
at cutoff or use signed multi insertion outputs. Provides compiler-ready
map from trajectory to actual reader. No claim of an all-order iterated
bound. All statements on Pencils are REAL statements. Use for any output
of Spine on the same Family and tags created before.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}{V: ℕ→Type}[∀ i,DecidableEq (V i)][∀ i,Fintype (V i)] {W:Type*}
    {D:Address.Rail C} {w:Worth}{r:ℕ→ℕ} {j b k g:ℕ}
set_option quotPrecheck false
local notation "Z₀"=> C.path.levels
local notation "X"=> C.path
local notation "t₁"=> C.path.levels.budget
local notation "K"=> C.path.levels.clock
local notation "τ₀"=> C.path.levels.clock.hatBeta
local notation "δ"=> renal C.path.levels
local notation "ψ"=> far C.path.levels
local notation "ζ"=> Legato.Bandage.fly C.path.levels
local notation "P!"=> C.side
local notation "Y"=> C.path.rep N p
local notation "ℓ"=> Copper.ld C.path.levels
local notation "O"=> Address.Bud C p
local notation "λ₀"=> C.path.levels.clock.op

variable (A:Planner C p n V W) (H:∀ i:ℕ,Census (V i)) (s:W→ℕ)(I:∀ i:ℕ,V i→ Body)
local notation "Λ"=>A.labelY
local notation "Φ"=>A.narrows
local notation "r₀"=>A.supportX
local notation "M₁"=> (apron C.path.levels)
local notation "M!"=> fun i:ℕ=> Config G (C.side i p)→Poly (H i)
variable {H}

structure Replay (hp:n≤b)(m:ℕ)(F:∀ i:ℕ, Config G (C.side i p)→Poly (H i))(N:ℕ): Prop where
    downhill (i:ℕ)(hi:b ≤ i)(hv:i < m ): let S := (A.narrows i (hp.trans hi)); ∃ hc:License (H i) (H (i+1)) (Prod.fst ∘ S),F i=downdraft (N:=N) A H s i (hp.trans hi) hc (F (i+1))

variable {f q:ℕ→ℝ}
local notation "w₀"=> west C q f k
variable (h:C.Makes) (hw:Storage C D)
-- constraints of radii and levels recorded precisely; growth gates have to write Replay with the licenses and furnish uniform limits.

structure Purse (C:Family G)(f q:ℕ→ℝ)(b m d k:ℕ):Prop where
   headV i : b ≤ i → i ≤ m → 0 < q i
   nextV i : b ≤ i → i < m → let L:ℝ:= (C.S.block i).val; q i ≤ L^d*q (i+1) ∧ q (i+1) ≤ L^d*q i
   upper i : b ≤ i → i≤ m → 0 < f i ∧ f i ≤ 1
   control i : b ≤ i → i < m → Refresh (C:=C) d k i ∧ 8 ≤ (C.path.levels.budget i).B

structure Toured (H:∀ i:ℕ,Census (V i))(hp:n ≤ b) (m:ℕ)(f:ℕ→ℝ)(k:ℕ):Prop where
   low_use i: b ≤ i→ i < m  → Occupancy (((K).op i p|>.ratio.parent) ∘ r₀ (i+1)) (M₁ i)
   high_use i : b ≤ i → i < m → Occupancy (r₀ (i+1)) (M₁ i)
   water i hi : i < m → Cushions A H hp i hi f k

abbrev Pens (C:Family G)(p:ℕ)(W:Type*):= W→∀ i:ℕ,Tape G (C.side i p)
structure Lantern (m N:ℕ)(q:ℕ→ℝ)(S:Pens C p W):Prop where
   brings (i:ℕ) : b≤ i→ i < m → ∀ (ht:i<N) (j:W),Train (D N p i ht) (keys0 h ht) (d:=s j) (S j (i+1)) (S j i) (Copper.ld C.path.levels i * (Copper.ld C.path.levels i*q i))
omit [(i:ℕ)→ DecidableEq (V i)] [(i:ℕ) → Fintype (V i)] in
lemma cap_lives (I:∀ i:ℕ,V i→ Body)(hp:n≤b)(hi:b ≤ i)(ht:i ≤ m) (hW:PreparedA A I b m hp) (hx:∀ j:V b, Cap (s (Λ b j)+2) (I b j) 1) : ∀ j:V i, Cap (s (Λ i j)+2) (I i j) 1:=by
    induction hi with
    | refl=> exact hx
    | step h ih=>
       rename_i i; intro j; have hs:=hp.trans h; rw [hW i h ht j,A.loyal i hs j]; have he:1 ≤ ((C.S.block i).val:ℝ):=by exact_mod_cast (C.S.block i).property
       apply cap_aff _ (by positivity) (inv_le_one_of_one_le₀ he) (Address.dist_box ..) (ih (Nat.le_of_succ_le ht) _)

variable (L':OPE.Package C w r D)
variable {F:∀ i:ℕ, Config G (C.side i p)→Poly (H i)}
local notation "Y!"=> fun i=> if i=m then (C.path.levels.budget i).supportExponent-4 else (C.path.levels.budget i).supportExponent
include hw h
set_option maxHeartbeats 650000 in
lemma session (hp:n≤b)(hi:m≤N)(T:Pens C p W) (he:Purse C f q b m d k) (ht:Toured A H hp m f k)(hl:Lantern s h (p:=p) (b:=b) (D:=D) m N q T) (hr:Replay (H:=H) A s hp m F N)
    (hS:∀ i,s i≤ d)(hP:PreparedA A I b m hp) (hW:∀ i:V b, Cap (s (Λ b i)+2) (I b i) 1)
    {x:ℝ}(hF:(t₁ m).supportExponent-4 ≤ x)(hv: MenuBoard (R:=H m) (Y m) (imprint h A I T m hi) (F m) (r₀ m) (fun _:V m=>w₀ m) x 1):
    ∀ j:ℕ, b ≤ j → ∀ hj:j≤ m, MenuBoard (R:=H j) (Y j) (imprint h A I T j (hj.trans hi)) (F j) (r₀ j) (fun _:V j=>w₀ j) (Y! j) 1:=by
    intro j hj hh; induction hh using Nat.decreasingInduction with
    | self=> obtain ⟨hma,hQ,J,Z,hT,hA,hr,r⟩:=hv; have hP:=mul_pos (he.upper m hj le_rfl).1 (grantw (k:=k) (C:=C) (m:=m) (he.headV m hj le_rfl)); refine ⟨hma,hQ,J,Z,hT,?_,?_,r⟩; all_goals simp only [if_true]; first | exact hA.shrink hF le_rfl (fun _=>hP) | exact hr.shrink hF le_rfl (fun _=>hP) -- hP all goals reorder
    | of_succ i hk ih=>
        obtain ⟨hc,hX⟩:= hr.downhill (V:=V) i hj hk
        have h₁:= (he.control _ hj hk).1; have hp' := he.nextV i hj hk; have hj':= hj.trans i.le_succ
        have hL: PreparedA A I b (i+1) hp:=fun j hᵢ hh Q=> hP j hᵢ (hh.trans_le hk) Q
        rw [hX,show (Y! i)= _ from if_neg (show i≠m from hk.ne)]
        apply day (N:=N) h hw A H s I T hp (hk.trans_le hi) hj (ih hj') ?_ (ht.water i hj hk) hc (ht.low_use _ hj hk) (ht.high_use _ hj hk) (he.control _ hj hk).2 hS hL (cap_lives A s I hp hj hk.le hP hW) (fun j=> hl.brings i hj hk (hk.trans_le hi) (Λ i j)) h₁ (he.upper _ hj hk.le).1 (he.upper _ hj' hk).1 (he.upper _ hj' hk).2 (he.headV _ hj hk.le) (he.headV _ hj' hk) hp'.1 hp'.2
        dsimp only; split; rfl; linarith

end YM.RG05Readout.Many
