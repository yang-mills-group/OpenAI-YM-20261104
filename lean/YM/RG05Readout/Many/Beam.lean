import YM.RG05Readout.Many.Reel
/-!
# Lit envelope chain launches Session

Prescribed backwards tuning at arbitrary level, with valuations externally
bounded through T charts. Actual Tune outputs are necessary, arbitrary
replacement doesn't drive Lesson. Uses the PYP horizon inverse, no positive
eigenmodel assumptions. Startup sees normalized top real stencil; at an
intermediate level use `session` instead.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {n m p N d:ℕ}{V: ℕ→Type}[∀ i,DecidableEq (V i)][∀ i,Fintype (V i)] {W:Type*}
    {D:Address.Rail C} {w:Worth}{r:ℕ→ℕ} {j b k g:ℕ}
set_option quotPrecheck false
local notation "Z₀"=> C.path.levels
local notation "X"=> C.path
local notation "t₁"=> C.path.levels.budget
local notation "K"=> C.path.levels.clock
local notation "τ₀"=> C.path.levels.clock.hatBeta
local notation "ρ"=> far C.path.levels
local notation "ζ"=> Legato.Bandage.fly C.path.levels
local notation "P!"=> C.side
local notation "Y"=> C.path.rep N p
local notation "ℓ"=> Copper.ld C.path.levels
local notation "O"=> Address.Bud C p
local notation "M₀"=> (apron C.path.levels)
variable (A:Planner C p n V W) {H:∀ i:ℕ,Census (V i)} (s:W→ℕ)(I:∀ i:ℕ,V i→ Body)
local notation "Λ"=>A.labelY
local notation "Φ"=>A.narrows
local notation "r₀"=>A.supportX
variable {f q:ℕ→ℝ}{B:ℕ→ℕ→ℝ}
local notation "w₀"=> west C q f k
variable (h:C.Makes) (L: OPE.Package C w r D) (hw:Storage C D)

def stages (U:(i:W)→Sight C (s i) p)(v:(i:W)→ℕ→Palette C (s i)): Pens C p W:= fun i j=> (U i j) (v i j)
structure Lesson (s:W→ℕ)(b m N p:ℕ)(T:Pens C p W)(B:ℕ→ℕ→ℝ)(Q:ℕ→ℝ)(v:(i:W)→ℕ→Palette C (s i)): Prop where
   billing j : ∃ U S, Spine D B h b p (s j) N U S ∧ (∀ i,T j i=(U i) (v j i)) ∧
        (∀ i, b≤ i → i < m → (S i) (v j (i+1)) = v j i)∧ ∀ i, b≤ i → i≤ m → size (v j i)≤ Q i
variable {v:(i:W)→ℕ→Palette C (s i)} {T:Pens C p W}
lemma Lesson.lights (he:Lesson (D:=D) h s b m N p T B q v): Lantern (D:=D) s h (b:=b) m N q T:=by
    refine ⟨fun i hk hm hr j=> ?_⟩; obtain ⟨U,S,hU,ht,hp,hq⟩:= he.billing j
    let z:=(v j (i+1)); have hx:= hU.follows i hk hr; rw [ht,ht, ← hp i hk hm]
    apply (hx.goes z).easier _
    have hp':0≤ℓ i:= zero_le_one.trans (lamp_nn _); apply mul_le_mul_of_nonneg_left _ hp'
    have hq':=(hx.strength z).1; rw [show S i z= _ from hp i hk hm] at hq'; exact hq'.trans (mul_le_mul_of_nonneg_left (hq i hk hm.le) hp')
variable {F:∀ i:ℕ,Config G (C.side i p) → Poly (H i)}
local notation "λ₀"=> fun i:V N=>stepUp (A.motion (Λ N i)) (r₀ N i) (entrance C (s (Λ N i)) N p (v (Λ N i) N) 0 (I N i))
local notation "Y!"=> fun i=> if i=N then (C.path.levels.budget i).supportExponent-4 else (C.path.levels.budget i).supportExponent
include h L hw
lemma dawn (hp:n≤b)(hi:b≤N)(he:Purse C f q b N d k)(hl:Lesson (D:=D) h s b N N p T B q v)
    (ht:∀ i≤ d,C.ref i≤N)(hW:∀ i:V b, Cap (s (Λ b i)+2) (I b i) 1)(hP:PreparedA A I b N hp)
    (hS:∀ i,s i≤ d)(hY:F N=birth (H N) (Y N) λ₀)(hx:∀ i≤ d,pricesTop ζ ρ N i ≤ (ρ N)*((τ₀ N)^k))
    (hO:Occupancy (r₀ N) (M₀ N)):
    MenuBoard (R:=H N) (Y N) (imprint h A I T N le_rfl) (F N) (r₀ N) (fun _:V N=>w₀ N) ((t₁ N).supportExponent-3) 1:=by
    have hf:= cap_lives A s I hp hi le_rfl hP hW
    have hQ(i:W): T i N=basisTop C (s i) N p (v i N) ∧ size (v i N) ≤ q N:=by
       obtain ⟨U,S,hU,hY,hF,hj⟩:=hl.billing i; rw [hY,hU.starts]; exact ⟨rfl,hj N hi le_rfl⟩
    have ha:= he.upper N hi le_rfl; have hb:= he.headV N hi le_rfl
    have hw'' : 0 < w₀ N:= mul_pos ha.1 (grantw hb)
    rw [hY]; unfold imprint; simp_rw [show ∀ i,T i N= _ from (fun i=>(hQ i).1)]
    apply initiate h L.system (s:=s ∘ Λ N) (e:=fun _=>1) (wheel h A N le_rfl) (fun i j hj=> ht j (hj.trans (hS _))) (m:=M₀ N) (t:=ρ N) ⟨hw.exactMoon.endow N⟩ hO (fun _=> hw'') hf _
    intro i; rw [one_mul]; let x':=v (Λ N i) N; let g:=τ₀ N; have hC:0 < g:= zero_lt_one.trans ((Z₀).fits.delayed _); have hκ: 0 ≤ ρ N:= (hw.exactMoon.endow N).1
    change w₀ N*(size x'*pricesTop ζ ρ N (s (Λ N i)))≤ρ N
    apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hx _ (hS _)) (size_ge _)) hw''.le)
    let U:= (ρ N)*(g^k); have hU:0 ≤ U:=mul_nonneg hκ (pow_pos hC _|>.le); let u':=f N
    apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hQ (Λ N i)|>.2) hU) hw''.le)
    refine (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (show 0 ≤ markWidth C N k (q N) from (grantw hb).le) (show u'≤1 from ha.2)) (mul_nonneg hb.le hU)).trans_eq ?_; change (g^k)⁻¹/q N* (q N * ((ρ) N*g^k))=_; field_simp
-- high-through endpoint
lemma assemble (hp:n≤b)(hi:b≤N)(he:Purse C f q b N d k)(hl:Lesson (D:=D) h s b N N p T B q v)
    (ht:∀ i≤ d,C.ref i≤N)(hS:∀ i,s i≤ d)
    (hW:∀ i:V b, Cap (s (Λ b i)+2) (I b i) 1)(hP:PreparedA A I b N hp)
    (hY:F N=birth (H N) (Y N) λ₀)(hx:∀ i≤ d,pricesTop ζ ρ N i ≤ (ρ N)*((τ₀ N)^k))
    (hO:Occupancy (r₀ N) (M₀ N))(hg:Toured A H hp N f k)(hr:Replay (H:=H) A s hp N F N):
    ∀ j:ℕ,b ≤ j →∀ hj:j ≤ N,MenuBoard (R:=H j) (Y j) (imprint h A I T j hj) (F j) (r₀ j) (fun _:V j=>w₀ j) (Y! j) 1:=
    session A s I h hw hp le_rfl T he hg (hl.lights s h) hr hS hP hW (show (t₁ N).supportExponent-4≤ (t₁ N).supportExponent-3 by linarith only) (dawn A s I h L hw hp hi he hl ht hW hP hS hY hx hO)
end YM.RG05Readout.Many
