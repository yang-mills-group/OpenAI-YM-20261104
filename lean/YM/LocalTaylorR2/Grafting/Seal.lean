import YM.LocalTaylorR2.Grafting.Kernel
/-! State usable at actual Family. still must be Redeemed.C. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Orbit
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive Candle
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ s κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Team R) (X:Coat T F) (H:Cash W s μ L Q o C T R)
    {Z : Support c} {k k':Finset ℕ}{u v : Air f G} (χ:Chi) (p:H.ThinP)
local notation "Θ"=>p.val
local notation "Ω"=> (M.signs S)
open _root_.YM.Marker Merge Switch Palette MergeProof Accent GridRenewal.Rain GridApprox.Nil
open Gas Ursell Trees
variable {ι Z:Type} [Fintype ι] [DecidableEq Z] (Y:ι→Leaf R)(u:ι→ℝ)(hU:Merge.Palette.Plot Y H u)
   (B:_root_.YM.Marker.Census Z)(z:ι→ _root_.YM.Marker.Poly B)
local notation "hd"=> Pressure.temp s
local notation "P!"=> Poly B
local notation "T!"=> turnWeight Y u
variable (l:ℕ)
variable (k:H.fragrances)
local notation "Θ'"=> reachability k
local notation "T'"=> Booking H Y l k -- check args
set_option quotPrecheck false
local notation "Z₀"=> Option (Fin k.1)
open Charge RG01.Survive.Products AnalyticBridge VerifiedReset Next.Foundations
variable {j k' m' n:ℕ} {θ ρ D K e v₀ d b r x Ct b' R' A c' δ :ℝ}
variable (hk:Marker.Tinted G s K d o.a L χ j)(U:StoresR2 H j v₀ d A D k' x n χ)
variable (N:Captain H j Ct d v₀ w A b r b' R' (n+j) χ) {ζ:ℝ}(hB:LocalBookingsR2 ζ c' N.conduit)
variable (h:1≤betaF G s L)(hζ:0≤ζ)(hH:1≤θ)(hp:1≤ρ)(hs:ρ*c'≤1)(hL: Charge.Allows l j θ)(hℓ: ρ^(l+1) ≤ betaF G s L^ζ)(hM:betaF G s L^ζ ≤ Real.exp (Q.mark L μ s))
-- direct sum Ring arithmetic (explicit filaments)
local notation "W₀"=> (fun i: H.ThinP=> totalBill H χ i N Y u K D θ ζ x ρ l)
variable (q₁:Z→ℝ)(hQ:∀ i,0<q₁ i)(hq:∀ i,Marker.Poly.price q₁ (z i) ≤ 1) (Ra:Z→Site c) (hr:∀ i, GridApprox.Nil.Scoped {x| Ra x∈(Y i).crest.image S.ratio.parent} (z i)) -- Ra shadows!
variable (ht: ∀ i,z i*z i=0)(h0:∀ i,(z i).part B.quiet=0) (R₀:Rep G c) [Fintype Z]
variable (K₀:ℝ → Finset ι→ Ovens.Code G c)
local notation "WU"=> measureS H χ Y u B z l
local notation "B₀" => R₀.p
local notation "pr0" => Quotes.preExponent (B₀)
local notation "A!"=> fullS H χ Y u B z l
local notation "E!"=> sketch H χ Y u B z l
local notation "p!"=> (fun f U=>Poly.pass (∑' i,cloaked H B (B₀) f i U))
local notation "w!"=> Mallow.straw μ L G s
open Tail
variable (wg: Reel.Scroll G f)
abbrev mainH := chef H χ Y u B z l (fun i=> apportion H Y l i (fun t=> if true=true then ¬l+1 ≤ t else l+1 ≤ t)) wg
abbrev errH:= A!- mainH H χ Y u B z l wg
local notation "ŷ"=> mainH H χ Y u B z l wg
local notation "ξ"=> errH H χ Y u B z l wg
-- re-express K (not estimated itself with wg change! it's frozen)
structure Adjusted (ε e v:ℝ) : Prop where
    stamp : RelayPaid H χ Y u B z l q₁ Ra R₀ K₀ ε v -- all unchanged.Tally
    tree : shop H B q₁ Ra (B₀) (ŷ) (betaF G s L^requested 0 ε)
    pass : shop H B q₁ Ra (B₀) (ξ) e ∧ Towed q₁ id (visitor H B R₀ (errH H χ Y u B z l wg)) R₀.p.B (Quotes.preExponent R₀.p) e
    exitU : Photo.spine Y H χ u B z= visitor H B R₀ (ξ)+ visitor H B R₀ (ŷ)
    ink (U:Config G c) : let H' :=cloaked H B R₀.p (ξ); let f:= refer H B R₀ (A!) (Photo.Fleece K₀ B z); Summable (fun i=>H' i U) ∧ f U=p! (ξ) U * refer H B R₀ (ŷ) (Photo.Fleece K₀ B z) U -- M notation function binder
local notation "K!"=> Photo.Fleece K₀ B z
variable {ε v e' x₀:ℝ} (hP: RelayPaid H χ Y u B z l q₁ Ra R₀ K₀ ε v) (hx:0 < x₀)
include hP hQ
lemma payBack (hY: shop H B q₁ Ra (B₀) (ŷ) (betaF G s L ^ requested 0 ε)) (hΩ: shop H B q₁ Ra (B₀) ((E! true)-(ŷ)) e') : Adjusted H χ Y u B z l q₁ Ra R₀ K₀ wg ε (e'+v) v:=by
   let Y' := (ŷ); let X:=(ξ); let Y'':=(E! true)
   let F' := cloaked H B (B₀); let P:= visitor H B R₀
   have hZ : shop H B q₁ Ra (B₀) X (e'+v):= by
       unfold X errH; rw [Orbit.part_doc]; convert! Orbit.shopPlus _ _ _ _ hΩ hP.stamp.pass.2 using 1; abel
   have hk : ∀ i:H.fragrances,F' (A!) i=F' X i + F' Y' i:=by
      intro i; ext1 U; by_cases hp:Healthy R₀.p.threshold (reachability i) U
      · unfold F' cloaked; rw [Pi.add_apply, masked_eq _ _ _ _ hp, masked_eq _ _ _ _ hp, masked_eq _ _ _ _ hp]; exact (sub_add_cancel ..).symm
      unfold F' cloaked; rw [Pi.add_apply,masked_ne _ _ _ _ hp, masked_ne _ _ _ _ hp, masked_ne _ _ _ _ hp,add_zero]
   have hr f a (h:shop H B q₁ Ra R₀.p f a)(U:Config G c): Summable (fun i=> F' f i U) ∧ (∑' i,F' f i U).part B.quiet=0:= by
      obtain ⟨hp,h⟩:= choir_ready H B q₁ Ra h; have ht:= (Towed.repair h hQ U).2; exact ⟨ht,(Poly.share ht _).trans (by simp only [(hp _).sil U, tsum_zero])⟩
   have hz (U:Config G c):=hr X _ hZ U; have hy(U:Config G c):=hr _ _ hY U
   refine ⟨hP,hY,⟨hZ,(viscera H B q₁ hQ Ra _ hZ).1⟩, ?_,?_⟩
   · rw [hP.tail.1]; ext1 i; ext1 U
     unfold visitor Accent.tally; simp only [Pi.add_apply]
     let A' := {q: H.fragrances // H.bookFoot (.inr q)=i}
     have hx : Summable (fun i:A'=> F' X i.1 U):= (hz U).1.comp_injective Subtype.val_injective; have he: Summable (fun i:A'=> F' Y' i.1 U):= (hy U).1.comp_injective Subtype.val_injective
     rw [← hx.tsum_add he]; exact tsum_congr fun i=>congr_fun (hk i.val) U
   intro U f q; refine ⟨(hz U).1,?_⟩; unfold q refer; rw [show (∑' i,cloaked H B R₀.p (A!) i U) = _ from (tsum_congr (fun i=> congr_fun (hk i) U)).trans ((hz U).1.tsum_add (hy U).1),Extra.Trajectories.pass_add (hz U).2 (hy U).2,mul_smul_comm,mul_assoc]
end YM.LocalTaylorR2.Orbit
