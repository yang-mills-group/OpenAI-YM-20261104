import YM.RG05Readout.Harvest.Feed
/-! Acquirer calls all profiles.Frozen common registries. Comes with true
 physical vector reporting proof and root-test license including volume
 normalization; don't use heading cost E for perturbative inverse beams
 without checked cross-frame statement.Same C/data.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Harvest
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Shadow Flatten Nuclear Halls Pulse
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {j b k l ℓ t t' o:ℕ}{e Q R x r r' a η ζ:ℝ}(h:C.Makes)
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "A!"=> C.S.a
local notation "Λ"=> C.S.toDepth
local notation "F₁"=> Site (C.side (n+1) p)
variable {D:Address.Rail C}{V I:Type}[DecidableEq V][Fintype V]{P: Address.Sight C d p}{S: Address.Emblems C d} (hm: n+1 < m)(hv:b ≤ n)(hN:m ≤ N)(ht:j ≤ b)
local notation "h₁"=>hm.le.trans hN
local notation "h₂"=> n.le_succ.trans hm.le
local notation "A"=> (n+1)
local notation "F!"=> Fintype.card (Color V)
local notation "Ω"=> Grip C p N n m b d j hm hv hN ht S
variable {B:ℕ→ℕ→ℝ}(hw: Awake D B b d)
variable {ψ:ℕ→ℕ}{w:Worth}(Yc:OPE.Package C w ψ D)(hC:Storage C D)(hS:Cater C D) (s:V→ℕ) (x:(i:V)→Palette C (s i)) (A₁:(i:V)→Sight C (s i) p)(U:(i:V)→ Emblems C (s i)) (hp:∀ i:V,size (x i)≤ Q)(hQ:0 < Q)
variable (h'A :∀ i:V,Spine D B h (n+1) p (s i) N (A₁ i) (U i))
    (hU:Spine D B h b p d N P S)(hg:d+3 ≤ C.path.levels.clock.J n)(hX:16*(1+t+Scope C ℓ) ≤ (C.S.toDepth ht p).count.val)(h_Open:Stock.Tabs.opens C.path.levels (bumper (2*t)) j b)(hPin: ∀ i,b≤ i→Pin C i d)
    (H:∀ u:V→Site (C.side (n+1) p), u∈ Pulse.area (C:=C) (p:=p) (b:=n+1) t' → Flock b n m p k d ℓ t (r*η/2) a C s u) -- maybe
    (he:0≤ thresholdC C (copperH C m n d ℓ k (Fintype.card (Color V)) Q) j b n d)(he':0≤ tender C m n d ℓ k (Fintype.card (Color V)) Q)
local notation "a!"=> tender C m n d ℓ k (F!) Q
local notation "e!"=> copperE C m n d ℓ k (F!) Q
local notation "q!"=> copperH C m n d ℓ k (F!) Q
local notation "τ"=> thresholdC C q! j b n d
local notation "f₁"=> fun i:V=>Many.point (U i) (x i) m N
local notation "L"=>Pulse.area (C:=C) (p:=p) (V:=V) (b:=n+1) t'
-- APIs use `hm,hv` entirely from Cut.Cut harmless waiting
noncomputable def taxLeaf (C:Family G)(t' m n o:ℕ)(s:V→ℕ)(r η:ℝ):ℝ:=
   ‖premiums C s m (n+1) r‖*((((Lattice.box t').card:ℝ))^Fintype.card V)*cutoffFee*earn s C (n+1) o η r
local notation "Y"=> taxLeaf C t' m n o s r η
variable (f: Wave V)(hs:(∑ i:V,(s i+2))+4*Fintype.card V<o+1)(hr:0<r)(hrP:r ≤ C.S.a (n+1))(hη:0<η)(hη':η≤1)(hζ:r*R+2*C.S.a (n+1)≤C.S.a (n+1)*t')
    (hF:Scattering f η)(hx: 0≤ζ)(hR:∀ x∈tsupport f.val,∀ i:V, ‖x i‖≤R)(hμ:Tall f (o+1) 1 ζ)
local notation "X"=>constellation (n:=n+1) s -- not valid
local notation "Q₁"=> constellation (C:=C) s f₁ r f h₁ m
include h hX h_Open hC hS Yc hPin h'A hU hw hg H he he' hp hQ hs hr hrP hη hη' hx hF hμ hR hζ
local notation "C!"=> printing C b n m d ℓ k (F!) (hv.trans h₂) Q (B d b)
set_option maxHeartbeats 540000 in
lemma witness_all : ∃ M: Palette C d, Ω Q₁ M (Y *a!* ζ) (Y*τ*ζ) (Y*C!*ζ):=by
    let a:=earn s C (n+1) o η r*ζ; have hp(u:V→F₁)(hv₁:u∈L): ∃ M:Palette C d, Ω (Pulse.meet (C:=C) s f₁ r f h₁ u) M (in_through a*a!) (in_through a*τ) (in_through a*C!):=by
        obtain ⟨G',hG,hY⟩:= regent s (C:=C) h₁ u r η f hr hrP hη hη' hs hF hx hμ
        obtain ⟨M,hM,hp'⟩:=feeds h hm hv hN ht hw Yc hC hS s x A₁ U hp hQ h'A hU hg hX h_Open hPin u (H u hv₁) he he' G' a hG; refine ⟨M, ?_⟩
        rw [← show org C p n N h₁ s f₁ u G'= Pulse.meet s f₁ r f h₁ u from ?_]; exact hM
        funext g i; unfold org Pulse.meet; apply setIntegral_congr_fun Pert.Cellular.cells_compact.measurableSet; intro v _; apply congr_arg; exact congr_fun (Pulse.cuts s f₁ u h₁ _ _ (hY v)) i
    choose! g hg using hp -- dependent subset automatic maybe h
    let I₁ i:= meet (C:=C) (p:=p) s f₁ r f h₁ i; let M:=∑ i∈L, g i; have hh:= Grip.all_sum hm hv hN ht L I₁ g (fun _=> in_through a*a!) (fun _=>in_through a*τ) (fun _=>in_through a*C!) hg h hw
    have hY: Q₁ =premiums C s m (n+1) r • ∑ i∈L,I₁ i:=funext fun i=>(stanza h₁ s f₁ r f hr hR t' m hζ i).trans (by simp only [Pi.smul_apply,Finset.sum_apply];rfl) -- args
    let p₁:= ‖premiums C s m (n+1) r‖*(in_through a); let a':= (↑(Lattice.box t').card:ℝ)^Fintype.card V; have hi: (↑(L).card:ℝ) ≤ a':=by unfold a'; exact_mod_cast Pulse.area_cost (C:=C) (p:=p) (b:=n+1) (V:=V) t'
    have hz:p₁ ≥ 0:=by
       let v : V→F₁:=fun _=>0; obtain ⟨G',hG,hF⟩:= regent s (C:=C) (p:=p) h₁ v r η f hr hrP hη hη' hs hF hx hμ; exact mul_nonneg (norm_nonneg _) (mul_nonneg (show 0 ≤ cutoffFee from add_nonneg zero_le_one ENNReal.toReal_nonneg) hG.pos)
    have htP := hh.scales hm hv hN ht _ hw (premiums C s m (n+1) r); refine ⟨premiums C s m (n+1) r • M, ?_⟩;rw [hY];apply htP.grow hm hv hN ht _
    · simp only [Finset.sum_const,nsmul_eq_mul]; apply le_trans (le_of_eq (b:= ((L).card:ℝ)*p₁*a!) (by unfold p₁; ring)); apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi hz) he'); unfold p₁ a a' in_through taxLeaf; exact le_of_eq (by ring)
    · simp only [Finset.sum_const,nsmul_eq_mul]; apply le_trans (le_of_eq (b:= ((L).card:ℝ)*p₁*τ) (by unfold p₁; ring)); apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi hz) he); unfold p₁ a a' in_through taxLeaf; exact le_of_eq (by ring)
    simp only [Finset.sum_const,nsmul_eq_mul]; apply le_trans (le_of_eq (b:= ((L).card:ℝ)*p₁*(C!)) (by unfold p₁; ring)); apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi hz) (show 0≤ C! from le_max_left ..)); unfold p₁ a a' in_through taxLeaf; exact le_of_eq (by ring)
end YM.RG05Readout.Harvest
