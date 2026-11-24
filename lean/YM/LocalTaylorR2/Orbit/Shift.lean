import YM.LocalTaylorR2.Orbit.Applied
/-! Under tally, not approximating later singleton regroup without paying for it. -/
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
local notation "P0"=> reachability (H:=H)
local notation "A!"=> fullS H χ Y u B z l
local notation "E!"=> sketch H χ Y u B z l
local notation "cl"=>cloaked H B R₀.p
include hQ
variable {V₀: H.fragrances→ Config G c→Poly B}
-- Downstream consumes precise shop.G through Spectrum; collapsed coefficients must carry support by actual labels. .tiedT on one representation.
abbrev visitor (F:H.fragrances→ Config G c→Poly B) := Accent.tally (fun i:H.fragrances=> H.bookFoot (.inr i)) (cl F)
omit [Fintype ι] [Fintype Z] in
lemma viscera (h: shop H B q₁ Ra R₀.p V₀ e): Towed q₁ id (visitor H B R₀ V₀) R₀.p.B (Quotes.preExponent R₀.p) e ∧ (∀ i, Burns Ra i (visitor H B R₀ V₀ i) R₀.p.threshold) :=by
   obtain ⟨hp,hA⟩:= choir_ready H B q₁ Ra h; refine ⟨towing (r:=id) _ _ hA hQ,?_⟩
   haveI : Countable H.fragrances:= by unfold Cash.fragrances Clusters Cash.ThinP; infer_instance
   intro i; exact transitE _ (r:=id) hp (fun U=> (Towed.repair hA hQ U).2) i
local notation "Δ"=>visitor H B (R₀)
local notation "K₀'"=> Mallow.straw μ L G s
open Tail
structure RelayPaid (ε v:ℝ):Prop where
   stamp : Budgeted H χ Y u B z l q₁ Ra R₀ K₀ ε v
   tail : Photo.spine Y H χ u B z= Δ (A!) ∧ Δ (A!)=Δ (E! true)+Δ (E! false) ∧
       Towed q₁ id (Δ (E! false)) R₀.p.B (Quotes.preExponent R₀.p) v
include ht h0 hU
lemma stores {ε v:ℝ} (h : Budgeted H χ Y u B z l q₁ Ra R₀ K₀ ε v)(hp:R₀.p.threshold=Pressure.temp s): RelayPaid H χ Y u B z l q₁ Ra R₀ K₀ ε v :=by
   refine ⟨h, ⟨congr_arg (Accent.tally _) (from_mask H χ Y u hU B z l ht h0 hp),?_, (viscera H B q₁ hQ Ra R₀ h.pass.2).1⟩⟩
   have he:= (choir_ready H B _ Ra h.pass.1).2
   have hV:= (choir_ready H B q₁ Ra h.pass.2).2
   ext1 i; ext1 U
   rw [h.partition]; unfold visitor Accent.tally
   simp only [Pi.add_apply]
   let X:= {p:H.fragrances// H.bookFoot (.inr p)=i}
   have hz : Summable fun j:X=>cl (E! true) j.1 U:= (Towed.repair he hQ U|>.2).comp_injective Subtype.val_injective
   have hA : Summable fun j:X=>cl (E! false) j.1 U:= (Towed.repair hV hQ U|>.2).comp_injective Subtype.val_injective
   rw [← hz.tsum_add hA]; apply tsum_congr; intro p; unfold cloaked -- .OR.Bound
   by_cases hp0:Healthy R₀.p.threshold (reachability p.val) U
   · rw [masked_eq _ _ _ _ hp0, masked_eq _ _ _ _ hp0, masked_eq _ _ _ _ hp0]; rfl
   rw [masked_ne _ _ _ _ hp0, masked_ne _ _ _ _ hp0, masked_ne _ _ _ _ hp0, add_zero]
end YM.LocalTaylorR2.Orbit
