import YM.LocalTaylorR2.Copper.Frost
import YM.LocalTaylorR2.Grafting.Shell
/-! Polynomial along Strand on actual support. Before transfer by rung. Uniform Complex-polynomial prices at output.
 Exact affine anchor count, all site modes. -/
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
-- collision `Reel.team/profiles`; qualify
open Reel (Filled Strand)
open Reel.Strand (dial)
abbrev answering (F':∀ k:H.fragrances,Finset (Booking H Y l k))(φ:Copper.Stems T):= fun i=> cameoS H χ Y u B z l i φ (F' i)
-- `E'=E` specialization true, on Moon filter

open Reel
variable {F': ∀ k:H.fragrances,Finset (Booking H Y l k)}(hF:∀ i q,q∈ F' i → ranked H Y l i q≤l)
variable (Φ:Reel.Strand→ Copper.Stems T)
variable (QF:∀ i:LogIndex c f, Filled (Reel.Pop H (H.supportP (identityLog i))) 1 dial (fun j=> Φ j i))
include N QF hF
-- explicit displacement. use stencil & row nerve
omit [Fintype ι] in
lemma swifter (i:B.Mode) (U₀:Config G c)(hv:Healthy hd (reachability k) U₀) : Filled ⊤ l dial (fun q=> tint U₀ (fun U=> (answering H χ Y u B z l F' (Φ q) k U).part i)):= by
   let W q:= Φ q; let U':= U₀; let v j q (V:Config G c):= (cameoSlice H χ Y u B z l k (W q) j V).part i
   have he q: (fun U=> (answering H χ Y u B z l F' (W q) k U).part i)= ∑ j∈F' k,v j q:=by funext x; unfold answering cameoS v; rw [Finset.sum_apply]; exact Poly.part_sum ..
   change Filled _ _ _ (fun q=>tint U₀ (fun U=>(answering H χ Y u B z l F' (W q) k U).part i))
   simp_rw [he,map_sum]; convert! Filled.group (P:=⊤) (w:=dial) (n:=l) (F' k) (fun x q=> tint U₀ (v x q)) ?h using 1; swap
   · intro j hi
     let X':=(petition H Y B z l k j).part i; let f q:= coeff H k • cameoC H χ Y u l k (W q) j
     have he : v j=fun k x=> f k x • X':=by funext m x; exact (Complex.real_smul ..).symm
     rw [he]; exact (plaster X' U₀ f ((fittedFor H χ Y u l k N Φ QF j U₀ hv).scaling _)).onward (hF _ _ hi)
   ext1 q; rw [Finset.sum_apply]
end YM.LocalTaylorR2.Orbit
