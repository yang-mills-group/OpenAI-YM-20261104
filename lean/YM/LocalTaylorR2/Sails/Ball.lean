import YM.LocalTaylorR2.Sails.Bract
import YM.LocalTaylorR2.Copper.Juice
import YM.LocalTaylorR2.Copper.Juicer
/-! adapted Orbit/Gateway. Before transfer by rung. Uniform Complex-polynomial prices at output.
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
local notation "t"=> Tickets (sign Y S)
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
-- Section Ra binder collision currently Ra:ℝ used N; rename Ra'
variable (wg:Copper.Stems T)
local notation "p₀"=> petition H Y B z l k
variable [Fintype Z]
local notation "WU"=> cameoS H χ Y u B z l k wg
variable (P':BudgetPoint) (he: P'.threshold=Pressure.temp s)(hJ:P'.order≤j)(hF:P'.B=radiusB s)(n':ℕ)(hn:P'.power≤n') (x':ℝ)(hy:0≤x')(hv:Sailor G P'.threshold x' j)(hZ:j*x' ≤ v₀)
local notation "a₀"=> wageScale H k P' j n'
local notation "fp"=> cCost H χ Y u l k N D x K θ
local notation "τ₀"=> (|coeff H k| *a₀)
local notation "m₀"=> frug H χ Y u B z l k N P' n' D x K θ -- check
variable {Icy:ℝ}(hI:1≤Icy)(hT:Exponent.Bank H j k' n x l m Icy) (hS:Exponent.Lodestar H m Icy N.conduit wg)
include hS hU hH hI hT he hJ hF hn hv hy hZ U hk
omit [Fintype Z] in
lemma modoP (q:T')(m:B.Mode)(o₁:Site c)(hx:o₁∈Θ'):
    let Y:=cameoSlice H χ Y u B z l k wg q; let Z':=fun U=>(Y U).part m; P'.Regular Θ' Z'∧ P'.supBounds o₁ Θ' Z' (m₀ q m):=by
  intro Y₀ Z'
  let W:(Config G c)→ℝ:= fun U=> coeff H k*cameoC H χ Y u l k wg q U
  let Y':ℂ:= (p₀ q).part m
  obtain ⟨hh,hp'⟩:= viaW H χ Y u hU l k hk U N hH wg hI hT hS P' he hJ hF n' hn x' hy hv hZ q o₁ hx
  have hy:P'.Regular Θ' W:= AnalyticBridge.CouplingShape.reg_scale (coeff H k) hh -- namespace check
  have hv : P'.supBounds o₁ Θ' W (|coeff H k| *(a₀*fp q)):= AnalyticBridge.CouplingShape.sup_scale (coeff H k) hp'
  rw [show Z'= Y' • (fun U:Config G c=>(W U:ℂ)) from funext fun _=> mul_comm ..]; refine ⟨regular_smul Y' (regular_mapped Complex.ofRealCLM hy),?_⟩
  unfold frug; rw [mul_assoc |coeff H k|]; exact bound_smul Y' ((sup_real hy).2 hv)
include hQ hq hℓ hM hB h hζ hp hs
omit [Fintype Z] in
lemma toyP (F:Finset (Booking H Y l k)) (r:ℕ)(hΩ : ∀ i∈F,r ≤ ranked H Y l k i):
    ∃ p : Sheet B, 0 ≤ p ∧ wordsPrice q₁ p ≤ (ρ^r)⁻¹ * LeafReady.allowance P' k j n' W₀ ∧
    ∀ m,let Z':=fun U=>(WU F U).part m; P'.Regular Θ' Z' ∧ ∀ (o:Site c), o∈ Θ' → P'.supBounds o Θ' Z' (p m):=by -- notation W₀ conflict section rℝ! depends on `r` through inferred Lean parameter? W₀ uses N capturing r old ok.
  let L m:= ∑ i∈F,m₀ i m
  have hp m o₁ (hy':o₁∈Θ'): let Z':=fun U=>(WU F U).part m; P'.Regular Θ' Z'∧P'.supBounds o₁ Θ' Z' (L m):=by
    intro J; rw [show J=∑ i∈F,(fun U=>(cameoSlice H χ Y u B z l k wg i U).part m) from funext fun j=>by unfold J cameoS;rw [Finset.sum_apply]; exact Poly.part_sum ..]; exact regular_bound_sum _ _ _ (fun i _=> modoP H χ Y u hU B z l k hk U N hH wg P' he hJ hF n' hn x' hy hv hZ hI hT hS i m o₁ hy')
  let x₀:=(Song.locate H k).site; have ha : x₀∈Θ':= (Song.locate H k).anchor
  have hy₀:= hy
  refine ⟨L,fun m=> (hp m x₀ ha).2.1, ?_,fun m=> ⟨(hp m x₀ ha).1, fun i h => (hp m i h).2⟩⟩
  unfold wordsPrice L; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; unfold frug
  let U₀:=fun i:Booking H Y l k=> (τ₀)*fp i
  have hX : 0≤ shiftG s:=by unfold shiftG; positivity
  have hh : 0≤ τ₀:= mul_nonneg (abs_nonneg _) (by unfold wageScale; positivity)
  calc _ = ∑ i∈F,Poly.price q₁ (p₀ i)*U₀ i:=by apply Finset.sum_congr rfl; intro i _; unfold Poly.price; rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun j _=> (mul_assoc ..).symm)
       _ ≤ ∑ i∈F,U₀ i:= Finset.sum_le_sum fun i _=> le_of_le_of_eq (mul_le_mul_of_nonneg_right (pet_price H Y B z l k q₁ hQ hq i) (mul_nonneg hh (c_nn H χ Y u hU l k hk U N hH i))) (one_mul _)
       _ ≤ (τ₀)*((ρ^r)⁻¹*∏ j':Z₀,(2^j*W₀ (k.2 j'))):=by unfold U₀; rw [← Finset.mul_sum];exact mul_le_mul_of_nonneg_left (c_bought H χ Y u hU l k hk U N hB h hζ hH ‹1≤ρ› ‹ρ*c'≤1› hℓ hM F hΩ) hh
       _ = _:= by
         unfold LeafReady.allowance clusters coeff wageScale; let D₀:=(ρ^r)⁻¹
         rw [abs_div,abs_of_nonneg (by positivity : (0:ℝ) ≤ ((k.1+1).factorial:ℝ))]; ring
end YM.LocalTaylorR2.Orbit
