import YM.RG05Readout.Many.Preflight
/-!
# Journey on tunes. For any fixed trajectory in the supply

Coordinates/T and continuation `Lit` at each step on actual polynomial,
with gauge ports witnessed per-root. Separations and any number of tiling
slots furnished as `Toured` proof. Here the support-budget unrolling accepts
generic profile kernels on each of the root lists (cartesian children, tests
in relative native root coordinates).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {n m p N d:ℕ}{V: ℕ→Type}[∀ i,DecidableEq (V i)][∀ i,Fintype (V i)] {W:Type*}
    {D:Address.Rail C} {w:Worth} {r:ℕ→ℕ}
set_option quotPrecheck false
local notation "Z₀"=> C.path.levels
local notation "X"=> C.path
local notation "t₁"=> C.path.levels.budget
local notation "K"=> C.path.levels.clock
local notation "β"=> C.path.levels.clock.hatBeta
local notation "δp"=> renal C.path.levels
local notation "ψ"=> far C.path.levels
local notation "ζ"=> fly C.path.levels
local notation "P"=> C.side
local notation "Y"=> C.path.rep N p
local notation "ℓ"=> Copper.ld C.path.levels
local notation "O"=> Address.Bud C p
variable (h:C.Makes) (hw:Storage C D)

-- AGE planner owns pick-hi proof; s labels external; orientation fixed per `original`. roots real at positions.
structure Planner (C:Family G)(p b:ℕ) (V:ℕ→Type)(W:Type*) where
   labelY : ∀ i:ℕ,V i→ W
   supportX : ∀ i:ℕ,V i→ Site (C.side i p)
   motion : W→ Motion
   narrows : ∀ i:ℕ,b ≤ i → V (i+1)≃V i×Address.Bud C p i
   loyal i hi x : labelY (i+1) x=labelY i (narrows i hi x).1
   future i hi x : supportX (i+1) x=affine (motion (labelY i (narrows i hi x).1)).1 ((C.path.levels.clock.op i p).ratio.embed (supportX i (narrows i hi x).1)) (Address.child C p i (narrows i hi x).2)
variable (A:Planner C p n V W)
local notation "Λ"=>A.labelY
local notation "Φ"=>A.narrows
local notation "r₀"=>A.supportX
local notation "M"=> (apron C.path.levels)
variable (H:∀ i:ℕ,Census (V i)) (s:W→ℕ)(I:∀ i:ℕ,V i→ Body) (T: W→∀ i:ℕ,Tape G (C.side i p))
local notation "v₀"=> (fun i:ℕ=> (K).op i p)
abbrev headFee (C:Family G) (p i:ℕ) (v:Address.Bud C p i) := Native.pull (Address.displacement C p i v) (((C.S.block i).val:ℝ)⁻¹)
def PreparedA (k l:ℕ)(hk:n ≤ k):Prop := ∀ i:ℕ,∀ hi:k≤ i,i<l→∀ x:V (i+1),I (i+1) x = headFee C p i (Φ i (hk.trans hi) x).2 (I i (Φ i (hk.trans hi) x).1)

-- h covariance key canonical determined. Does not constrain other K-choices besides printed board.
noncomputable def wheel (i:ℕ)(hi:i ≤ N) (j:V i) : (C.path.rep N p i).activities.Moves (A.motion (A.labelY i j)).1 (r₀ i j):=Classical.choice ((h.wilson.represents _ _ _ hi).good.labels.moves _ _)
def imprint (i:ℕ)(hi:i ≤ N)(j:V i):Three G (C.side i p):= View.spin (A.motion (Λ i j)) (wheel h A i hi j) ((T (Λ i j) i) (I i j))
def downdraft (i:ℕ)(hl:n ≤ i)(hp:License (H i) (H (i+1)) (Prod.fst ∘ (Φ i hl))) (F:Config G (C.side (i+1) p)→Poly (H (i+1))) : Config G (C.side i p)→Poly (H i):=fun U=>feed (fun x=> budwgt C p i (s (Λ i ((Φ i hl) x).1))) hp (((v₀ i).push ((Y (i+1)).beta) F) U)
-- hm used? remove mark step hm or nolinter. h in wheel proof only.
variable {x q f :ℕ→ℝ}{k b g j:ℕ}
-- allowance each step Levy, even if disabled restore by modifier. Exact arithmetic.
inductive Cushions (hp:n≤b)(i:ℕ)(hi:b ≤ i) (f:ℕ→ℝ)(k:ℕ):Prop where
    | via (ht:Drake (H (i+1)) (t₁ i|>.B) ((v₀ i|>.ratio.parent) ∘ (r₀ (i+1)))) (hw:f i ≤ f (i+1)): Cushions hp i hi f k
    | straight (ht:f i ≤ f (i+1) * ((β i)^(3*k+4))⁻¹) : Cushions hp i hi f k
-- simpler theorem statement budget unlike shelf restoration

def west (C:Family G)(q f:ℕ→ℝ)(k i:ℕ):= f i * markWidth C i k (q i)
local notation "w₀"=> west C q f k
lemma grantw {Q:ℝ}{k:ℕ}(hy:0<Q): 0< markWidth C m k Q :=div_pos (inv_pos.mpr (pow_pos (zero_lt_one.trans ((Z₀).fits.delayed _)) _)) hy

include h hw
set_option maxHeartbeats 700000 in
lemma day {e:ℝ} {B':Config G (C.side (m+1) p) → Poly (H (m+1))}
    (hp:n≤b) (hm:m<N)(hi:b≤ m)(hb:MenuBoard (Y (m+1)) (imprint h A I T (m+1) hm) B' (r₀ (m+1)) (fun _:V (m+1)=>w₀ (m+1)) e 1) -- B' e undeclared
    (hx:(t₁ (m+1)).supportExponent-4 ≤ e)
    (hc:Cushions A H hp m hi f k)
    (hr:License (H m) (H (m+1)) (Prod.fst ∘ Φ m (hp.trans hi)))
    (hg:Occupancy ((v₀ m).ratio.parent ∘ (r₀ (m+1))) (M m)) (hG: Occupancy (r₀ (m+1)) (M m)) (hB:8 ≤ (t₁ m).B) (hS:∀ i,s i ≤ d)
    (hP:PreparedA A I b (m+1) hp) (hW:∀ i:V m, Cap (s (Λ m i)+2) (I m i) 1)
    (hD:∀ i:V m,Train (d:=s (Λ m i)) (D N p m hm) (keys0 h hm) (T (Λ m i) (m+1)) (T (Λ m i) m) (ℓ m * (ℓ m * q m)))
    (hF: Refresh (C:=C) d k m)
    (ht:0<f m)(htu:0<f (m+1))(ht': f (m+1) ≤ 1)(hY:0<q m)(hy: 0< q (m+1))(ha:q m ≤ ((C.S.block m).val:ℝ)^d * q (m+1)) (hz:q (m+1) ≤ ((C.S.block m).val:ℝ)^d*q m):
    MenuBoard (Y m) (imprint h A I T m hm.le) (downdraft (N:=N) A H s m (hp.trans hi) hr B') (r₀ m) (fun _:V m=>w₀ m) (t₁ m|>.supportExponent) 1:=by
    obtain ⟨s',t,hv⟩:= hw.exactMoon.days N p m hm
    have hf : Coursework X M (D N p m hm) ((δp) m) s' t := ⟨hv.2,hv.1⟩
    have hw' : 0 < w₀ (m+1):=mul_pos htu (grantw hy); have hW': 0 < w₀ m:= mul_pos ht (grantw hY)
    let L:ℝ:= (C.S.block m).val; let η :ℝ:= w₀ m*L^d; have hL:1 ≤ L:=by unfold L; exact_mod_cast (C.S.block m).property
    have hη : 0 < η:= mul_pos hW' (pow_pos (zero_lt_one.trans_le hL) _)
    let g:= Prod.fst ∘ (Φ m (hp.trans hi))
    let O':= ((v₀ m).ratio.parent) ∘ (r₀ (m+1)); have heO: O'=r₀ m ∘ g:=parentExact (δ:=A.motion ∘ Λ m) (A.future m (hp.trans hi))
    let r:= fun _: V (m+1)=>η
    have hv' : Repegs (r₀ m ∘ g) ((t₁ m).B) (fun _=> δp m * w₀ (m+1)) r (1/2) 1 (H (m+1)):=by
       rw [← heO]; rcases hc with ⟨he,hx⟩ | ⟨hx⟩
       · apply he.palms _ (fun _=> hη) (fun _=>mul_pos hv.2.hats.1 hw') hB; intro i; change f m * markWidth C m k (q m) * L^d ≤ _; rw [mul_assoc]
         have hj:= hF.restoration (q m) (q (m+1)) hY hy hz
         have hh := mul_le_mul hx hj (show 0 ≤ markWidth C m k (q m)*L^d from by have he:=grantw (C:=C) (m:=m) (k:=k) hY; have h':0<L:=zero_lt_one.trans_le hL; positivity) (le_of_lt htu); exact hh.trans_eq (by unfold west; ring)
       let z:=fun _: V (m+1)=> δp m* w₀ (m+1); have hz': ∀ i,η≤z i:=by
           intro i; unfold η z west;rw [mul_assoc]
           let D':=(β m)^(3*k+4)
           have he:=grantw (C:=C) (m:=m) (k:=k) hY; have hf:0 ≤ markWidth C m k (q m)*L^d:=mul_nonneg he.le (pow_nonneg (zero_le_one.trans hL) _)
           refine ((mul_le_mul_of_nonneg_right hx hf).trans (le_trans (b:=f (m+1)*(markWidth C m k (q m)*L^d /D')) (le_of_eq ?_) ?_))
           unfold D'; ring
           have h:=hF.sacrifice (q m) (q (m+1)) hY hy hz
           exact (mul_le_mul_of_nonneg_left h htu.le).trans_eq (mul_left_comm ..)
       intro i _ j _; rw [one_mul]; exact le_trans (Finset.prod_le_prod (fun _ _=>hη.le) (fun i _=> hz' i)) (le_mul_of_one_le_right (Poly.worth (fun i=>hη.trans_le (hz' i)) i).le (Real.one_le_exp (by positivity)))
    let μ i:= wheel h A m hm.le i; let t i : Tape G (C.side (m+1) p):= T (Λ m i) (m+1)
    have hU(i: V (m+1)): Signpost (Y (m+1)) (A.motion (Λ m (g i))) (r₀ (m+1) i) ((T (Λ m (g i)) (m+1)) (headFee C p m (Φ m (hp.trans hi) i).2 (I m (g i)))) (imprint h A I T _ hm i):=by
       have he':Λ (m+1) i=Λ m (g i):=A.loyal m (hp.trans hi) i
       rw [← show I (m+1) i= headFee C p m (Φ m (hp.trans hi) i).2 (I m (g i)) from hP m hi (Nat.lt_succ_self _) i, ← he']
       exact View.spin_at ..
    apply advance (s:=s ∘ Λ m) (T:=t) (ν:=Φ m (hp.trans hi)) h hf μ hm hD hb hx hg hG (A.future m (hp.trans hi)) hr hU (B₁:=fun _=>1) hW (fun _=>hw') (fun _=>hη) hv' _ (fun _=> hW') (fun i=> mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (hS _)) hW'.le)
    intro i; simpa only [mul_one,west] using hF.first (q m) (q (m+1)) (f (m+1)) hY hy ht' htu ha
end YM.RG05Readout.Many
