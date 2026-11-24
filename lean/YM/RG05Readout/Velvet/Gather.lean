import YM.RG05Readout.Velvet.Saver
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Velvet
open Function MeasureTheory Set Filter Topology Pulse Native Address Many Lattice Wilson Extraction WithLp Nuclear Bay Cells Harvest Halls
open RG MergeProof Flatten PhysicalNext.Repeat Legato Dash Extraction.Lease Petals Push.RelayDifference -- Storage
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{i m n j b d k ℓ t t' v o N p:ℕ}
    {Q q R r η ζ B':ℝ}(h:C.Makes){D:Address.Rail C}{ψ:ℕ→ℕ}{w:Bid.Worth}
  (A:OPE.Package C w ψ D)(hA:Storage C D)(hp:Cater C D) {f : Extraction.Order}{B:ℕ→ℕ→ℝ}
local notation "δ"=> C.S.a
local notation "I"=> Fin v
local notation "P"=> (i:I)→Palette C
local notation "Φ'"=> Wave (Fin v)
local notation "a!"=> (C.S.a j/8)
variable (F:Wave (Fin v))(s: Fin v→ℕ)(x:(i:Fin v)→ Palette C (s i))
section
open Chalice
variable {b₀:ℕ→ℕ} (Y:∀ d:ℕ,Cutoffs→ Address.Emblems C d)
/-- Campaign exact single product packet read to ANY regulator from the anchored TRUE basis. -/
def hears (n m b d N p:ℕ) (q:ℝ)(M:Palette C d) := ∃ h:n+1≤N,
    Report C p N n m b d (Y d (N,p)) (constellation s (fun i=> Many.point (Y (s i) (N,p)) (x i) m N) q F h m) M
local notation "M1"=>rebases C n m d * mSeat C s Q m n o d t' ℓ k η q
local notation "M2"=>mBirth C s Q m n o d t' ℓ k η q j b
variable (hY:Chalice.Anchored D B h b₀ Y)(hh:∀ i:Fin v,b₀ (s i) ≤ b)(he:b₀ d ≤ b)
    (hR:∀ p:ℕ, Right C p n m j b k ℓ t t' d s q R (C.S.a j/8) η B' Q)
variable (hx:∀ i:Fin v,size (x i)≤ Q)
    (hF : Sky F R η)(hz:0≤ζ)(hZ:Tall F (o+1) 1 ζ)(ho: (∑ i:Fin v,(s i+2))+4*v < o+1)
local notation "P!"=> fun i:Fin v=> Many.point (Y (s i) (N,p)) (x i) m N
local notation "R!"=>hears F s x Y n m b d N p q
local notation "ξ"=>physicalEra q F
local notation "Φ"=>fun (g:Body)(M:Palette C d)=> physicalEra q F g C m p N s P! - fieldC C m N p d (fastU (Y d) (fun _=>M) m (N,p)) g
include h hY he
lemma hears_only {x' y:Palette C d}(h_x:R! x')(h_y:R! y): x'=y:=by
    obtain ⟨hw,hx⟩:=h_x; obtain ⟨hp,hP⟩:=h_y
    exact Report.identical _ (ongoing (hY.age d) he) hx hP
include A hA hp hR hh hx hF hZ hz ho
lemma honorable (ht:m ≤ N)(p:ℕ): let hw:=hR p; let T:= Push.GridApprox.tilesAt C.S p (((hw.h_b.trans hw.hv).trans (Nat.le_trans (Nat.le_add_right n 1) hw.east.le)).trans ht); ∃ M:Palette C d, hears F s x Y n m b d N p q M ∧ size M ≤ M1*ζ ∧ ∀ g:Body, (∀ x∈tsupport g.val,‖x‖≤ a!) → Tall (E:=E4) g (d+2) 1 1→
    let v:=fun i:Fin v=> Many.point (Y (s i) (N,p)) (x i) m N; let z:= physicalEra q F g C m p N s v-fieldC C m N p d (Many.point (Y d (N,p)) M m N) g; Interior (T.chamber 0) z∧ T.rootTest (C.beta N p) z ≤ M2*ζ:=by
    intro hw T; let i:Cutoffs:=(N,p); have ht0:= hw.east.le.trans ht; have ht1:= hw.hv.trans n.le_succ; have h1:Spine D B h b p d N _ (Y d i):= Records.Spine.tail h _ _ (hY.paid i d (he.trans (ht1.trans ht0))).choose_spec he
    have hx'(j:Fin v): Spine D B h (n+1) p (s j) N _ (Y (s j) i):=Records.Spine.tail h _ _ (hY.paid i (s j) ((hh j).trans (ht1.trans ht0))).choose_spec ((hh j).trans ht1)
    obtain ⟨M,hM,h_M,hc⟩:=bulletin h A hA hp s x _ _ hx hx' h1 (ongoing (hY.age d) he) hw ht F hF.shape hz hZ hF.spread (by simpa using ho)
    exact ⟨M,⟨ht0,hM⟩,h_M,hc⟩
variable (x':Cutoffs→ Palette C d)
local notation "X"=> fun i:Fin v=>fastU (Y (s i)) (fun _=>x i) m
local notation "U"=> fun i:Cutoffs=>fieldC C m i.1 i.2 d (fastU (Y d) x' m i)
local notation "V"=> fun (i:Cutoffs)(g:Body)=> physicalEra q F g C m i.2 i.1 s (fun j=> (X j i))
lemma paid_value (hr:∀ᶠ i:Cutoffs in f.fuse,hears F s x Y n m b d i.1 i.2 q (x' i)) : ∀ᶠ i in f.fuse, size (x' i)≤ M1 *ζ:=by
    filter_upwards [hr,(Push.RelayDifference.cutoff_grows _).eventually_ge_atTop m] with i hi hh_N; obtain ⟨M,hx,hK,-⟩:=honorable h A hA hp F s x Y hY hh he hR hx hF hz hZ ho hh_N i.snd; rw [hears_only h F s x Y hY he hi hx]; exact hK
variable (H:CenterPort C f)(L:Poem C j)(S:ℝ)
noncomputable def backing (L:Poem C j)(h:C.Makes)(H:CenterPort C f)(d:ℕ):ℝ := (leaning h L H).choose * (opening_gain L d).choose
include H
omit A hA hp hR hh hx hF hZ hz ho he hY in
lemma backing_nn : 0 ≤ backing L h H d := mul_nonneg (leaning h L H).choose_spec.1 (opening_gain L d).choose_spec.1.le
local notation "L'"=>L.opening
-- prepaid for EVERY possible census
lemma allotment (hr:∀ᶠ i:Cutoffs in f.fuse,hears F s x Y n m b d i.1 i.2 q (x' i)): ∀ᶠ i in f.fuse,
    ‖preamble L i.1 i.2 (V i L')-preamble L i.1 i.2 (U i L')‖ ≤ backing L h H d*(M2*ζ):=by
       let A₁:= (opening_gain L d).choose; obtain ⟨ha,g,hG,hg,h_p⟩:= (opening_gain L d).choose_spec
       obtain ⟨hK,hK'⟩:= (leaning h L H).choose_spec
       filter_upwards [hr,(Push.RelayDifference.cutoff_grows f).eventually_ge_atTop m,hK'] with i hi hh_N hL; rcases i with ⟨N,p⟩; let r:Cutoffs:=(N,p); obtain ⟨x,hx,h_X,hP⟩:=honorable h A hA hp F s x Y hY hh he hR hx hF hz hZ ho hh_N p; obtain ⟨hh',hv⟩:=hL; let T:=center C.S p hh' 0; specialize hP g h_p hg; let B':ℂ:=A₁
       have he' : x=x' r:= hears_only h F s _ Y hY he hx hi; rw [he'] at hP
       let z:= V r g-U r g; have hf: V r L'-U r L'= B' • z:=by unfold z; rw [hG,smul_sub]; dsimp only; rw [quoted F s, Petals.saleOne] -- expected order
       let K:= (leaning h L H).choose; have hD : T.rootTest (C.beta N p) (V r L'-U r L')≤ A₁*(M2*ζ):= by rw [hf,Next.Extract.root_smul,Complex.norm_real, Real.norm_of_nonneg ha.le]; exact mul_le_mul_of_nonneg_left hP.2 ha.le
       rw [← onward_minus L _ _ (sweep h _ _ L (X) q) (minting _ _)]; apply (hv _ (hf.symm ▸ hP.1.scale B')).trans; exact (mul_le_mul_of_nonneg_left hD hK).trans_eq (mul_assoc ..).symm
end
end YM.RG05Readout.Velvet
