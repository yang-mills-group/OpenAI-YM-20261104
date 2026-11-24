import YM.RG05Readout.Harvest.Payables
/-!
# Exact licensed bulletin for RG detection.E1 part

No extra perturbative inputs assumed for this bulletin. Requires hOpen etc
 at fixed reading levels. Uniform in stated Tall and geometry on common
 regenerated C.B.Horizons.TEE expos. Along all-phase layout center_0 only
 at finite torus.Meta.MS.Graph E1 reclosure on other path not inferred.
 Packet O.E2 downstream. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Harvest
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Shadow Flatten Nuclear Halls Pulse OPE
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d o:ℕ}
    {j b k ℓ t t':ℕ}{q e Q B' R a η ζ:ℝ}(h:C.Makes)
set_option quotPrecheck false
local notation "X"=> C.path.levels
local notation "A"=> C.S.a
local notation "Λ"=> C.S.toDepth
variable {D:Address.Rail C}{V:Type}[Fintype V][DecidableEq V]{P:Address.Sight C d p}
    {S:Address.Emblems C d}{B:ℕ→ℕ→ℝ}
local notation "V!"=> Fintype.card (Color V)
local notation "Y!"=> rebases C n m d
/-- This exact geometry supplies calibration up to finite regulator. -/
structure Right (C:Family G)(p n m j b k ℓ t t' d:ℕ)(s:V→ℕ)(q R z η a Q:ℝ):Prop where
    pays :0<Q
    h : 0<q
    reach : q ≤ C.S.a (n+1)
    hv : b ≤ n
    east : n+1 < m
    stage : d+3 ≤ C.path.levels.clock.J n
    h_b : j ≤ b
    beam : 16*(1+t+Scope C ℓ) ≤ (C.S.toDepth h_b p).count.val
    opens : Stock.Tabs.opens C.path.levels (bumper (2*t)) j b
    pins : ∀ i,b≤ i → Pin C i d
    proximal : ∀ u: V→ Site (C.side (n+1) p), u∈Pulse.area (C:=C) (p:=p) (b:=n+1) t'→ Flock b n m p k d ℓ t (q*η/2) a C s u
    pos : 0<η
    locked : η≤1
    earth : q*R+2*C.S.a (n+1)≤ C.S.a (n+1)*t'
    free :0< Halls.copperH C m n d ℓ k (Fintype.card (Color V)) Q
    wicks : 0 ≤ Halls.tender C m n d ℓ k (Fintype.card (Color V)) Q
    meet : q*R+2*C.S.a (n+1)< C.S.radius p
    bound : z+q*R<C.S.radius p
    move : z+C.S.a b ≤ C.S.a j /4
    tune : z+C.S.a b*3 < C.S.radius p
-- All discrete target factors. Tie one
structure Report (C:Family G)(p N n m b d:ℕ)(U:Address.Emblems C d)(F:Bin G (C.side N p))(c:Palette C d):Prop where
    boundary : b≤n
    h : n ≤ m
    cover : n+1≤N
    storied : Sees C p N n m b d h boundary cover U F ((↑(rebases C n m d):ℂ)⁻¹ • c)
lemma rebases_pos : 0 < rebases C n m d :=pow_pos (div_pos (C.S.a_pos _) (C.S.a_pos _)) _
lemma Report.identical (Y:Bin G (C.side N p))(hw:Awake D B b d){P': Emblems C d}{x y}(hx:Report C p N n m b d P' Y x)(hp:Report C p N n m b d P' Y y):x=y:=by
    obtain ⟨ha,hb,hc,hK⟩:=hx; obtain ⟨h1,h2,h3,heV⟩:=hp; exact smul_right_injective _ (inv_ne_zero (Complex.ofReal_ne_zero.mpr rebases_pos.ne')) (hK.unique hb ha hc Y hw heV)
variable {ψ:ℕ→ℕ}{w:Worth}(Yc:OPE.Package C w ψ D)(hC:Storage C D)(hS:Cater C D) (s:V→ℕ) (x:(i:V)→Palette C (s i)) (A₁:(i:V)→Sight C (s i) p)(U:(i:V)→ Emblems C (s i))
    (hx:∀ i:V,size (x i)≤ Q) (hA:∀ i:V,Spine D B h (n+1) p (s i) N (A₁ i) (U i))
    (hU:Spine D B h b p d N P S)(hw: Awake D B b d)
    (H:Right C p n m j b k ℓ t t' d s q R B' η a Q)
    (hN:m ≤ N)
local notation "f₁"=> fun i:V=>Many.point (U i) (x i) m N
local notation "h₁"=> H.east.le.trans hN
local notation "ht"=> H.h_b
local notation "K"=> ((H.h_b.trans H.hv).trans n.le_succ).trans (H.east.le.trans hN)
local notation "a!"=> tender C m n d ℓ k V! Q
local notation "L!"=>taxLeaf C t' m n o s q η
local notation "V₁"=> thresholdC C (copperH C m n d ℓ k V! Q) j b n d
local notation "P₀"=> mSeat C s Q m n o d t' ℓ k η q
local notation "P₁"=> mBirth C s Q m n o d t' ℓ k η q j b
variable (f:Wave V) (hξ:∀ x∈tsupport f.val,∀ i:V,‖x i‖≤ R)(hζ:0 ≤ ζ)(htP:Tall f (o+1) 1 ζ) (hΨ:Scattering f η)(hs:(∑ i:V,(s i+2))+4*Fintype.card V < o+1)
local notation "Z"=>constellation (C:=C) s f₁ q f h₁ m
include h hC Yc hS hw hA hU hx H hN hs hζ htP hΨ hξ
lemma bulletin : ∃ M, Report C p N n m b d S Z M∧ size M ≤ (Y! * P₀)*ζ ∧ ∀ g:Body, (∀ x∈ tsupport g.val, ‖x‖≤ B') → Tall (E:=E4) g (d+2) 1 1 →
    let T:= GridApprox.tilesAt C.S p K
    let W:= physicalEra q f g C m p N s f₁-fieldC C m N p d (Many.point S M m N) g
    Interior (T.chamber 0) W ∧ T.rootTest (C.beta N p) W ≤ P₁*ζ:=by
    have ht':0≤ V₁:=div_nonneg (Real.exp_pos _).le (focus_ge H.free).le
    obtain ⟨M,hM⟩:=witness_all h H.east H.hv hN ht hw Yc hC hS s x A₁ U hx H.pays hA hU H.stage H.beam H.opens H.pins H.proximal ht' H.wicks f hs H.h H.reach H.pos H.locked H.earth hΨ hζ hξ htP
    let v:= (↑(rebases C n m d):ℂ); have hv':v ≠ 0:= Complex.ofReal_ne_zero.mpr rebases_pos.ne'; refine ⟨v • M,⟨H.hv, le_trans n.le_succ H.east.le,H.east.le.trans hN,?_⟩,?_,fun g hg hP=>?_⟩
    · rw [show _⁻¹ • (v • M)=M from inv_smul_smul₀ hv' M]; exact hM.info
    · rw [size_smul]; refine le_trans (mul_le_mul_of_nonneg_left hM.price (norm_nonneg _)) (le_of_eq ?_); unfold v; rw [Complex.norm_real,Real.norm_of_nonneg rebases_pos.le, ← mul_assoc]; rfl
    let T:= GridApprox.tilesAt C.S p K
    have he:0 ≤ L!*V₁*ζ:=by
        let z:Site (C.side b p):=0; have hS:separation z 0 ≤ (Λ ht p).count.val/4:=by simp [z]
        have hp:= hM.presence z hS 0 ((zero_basis _).increase zero_le_one);
        exact (T.root_nonneg ..).trans hp.2 -- newline
    obtain ⟨hx,hQ⟩:= render h S H.east H.hv hN ht s x U f g q H.meet H.bound hξ H.h hg H.move H.tune he hM hP; dsimp only
    refine ⟨hx,hQ.trans_eq ?_⟩; unfold mBirth; ring
end YM.RG05Readout.Harvest
