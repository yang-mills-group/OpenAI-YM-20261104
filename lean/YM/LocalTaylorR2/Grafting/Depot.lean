import YM.LocalTaylorR2.Grafting.Craft
import YM.LocalTaylorR2.Grafting.Rise
import YM.MergeProof.Sate
/-! Adapted from Orbit/Casting and Applied. Coefficient-special budget to the ACTUAL Pack at Stope. Includes all Cipher.marker derivative loans. -/
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
open Reserves Tender LeafReady
variable {a wN:ℝ} (P':BudgetPoint) (he: P'.threshold=Pressure.temp s)(hJ:P'.order≤j)(hF:P'.B=radiusB s)(n':ℕ)(hn:P'.power≤n') (x':ℝ)(hy:0≤x')(hv:Sailor G P'.threshold x' j)(hZ:j*x' ≤ v₀) (h₁:0<δ) (h₂: Quotes.preExponent P' ≤ a)
local notation "vS" => allowance P' (H:=H)
variable [Fintype Z] (F': ∀ k:H.fragrances, Finset (Booking H Y l k))
local notation "pr0"=> Quotes.preExponent P'
variable (wg:Reel.Scroll G f)
local notation "WU"=> fun (k:H.fragrances)=>blueS H χ Y u B z l k wg
variable {J':Cash W s μ L Q o C T (Reel.bend R wg)} {Ξ':Utopia J' j v₀ d r Ct χ}{z₀':ℝ}
  (hq':∀ i,Ξ'.goalsL i ≤ N.conduit.goalsL i)(hN:LocalBookingsR2 ζ z₀' Ξ')
include J' hq' hN
include hU h hr hQ hq hk U hB hζ hH hp hs hL hℓ hM he hJ hF hn hv hy hZ h₁ h₂
lemma blueBooks (hY: Ready H.smallAt P'.B (fun i=>2^j* W₀ i) (a+δ) wN δ (1/2)) (r:ℕ)(hc:∀ i q,q∈F' i → r ≤ ranked H Y l i q): shop H B q₁ Ra P' (fun i=> (WU) i (F' i)) ((ρ^r)⁻¹*(collars G δ s j n'*(wN*(1-1/2:ℝ)⁻¹))) :=by
  have hr i:= blue_ret H χ Y u B z l i _ hr wg (F' i)
  choose u hP ht hX using fun i=> blue_array H χ Y u hU B z l i hk U N hB h hζ hH hp hs hL hℓ hM q₁ hQ hq wg P' he hJ hF n' hn x' hy hv hZ hq' hN (F' i) r (hc i)
  let f i:= (ρ^r)⁻¹*allowance P' i j n' W₀ -- local notation capture
  have hv:= hitsA H P' n' W₀ hY r h₁ h₂ hp
  have hf i:0≤f i:= (show 0≤ wordsPrice q₁ (u i) from sum_nonneg (fun j _=> mul_nonneg (Poly.worth hQ _).le (hP i j))).trans (ht i)
  refine ⟨f, ?_,hv,fun i=> ⟨_,hP i,ht i,hX i,hr i⟩⟩
  have hD : ∀ i:H.fragrances,(reachability i).Nonempty := fun i=> ⟨_,(Song.locate H i).anchor⟩
  have hf' := Product.everyone_ne _ _ hf (fun i _=> hD i) hv
  exact hf'.2.1.of_nonneg_of_le hf (fun i=> le_mul_of_one_le_right (hf i) (Real.one_le_exp (mul_nonneg (show 0 ≤pr0 from by unfold Quotes.preExponent; have h:= P'.exponent_pos; positivity) (Nat.cast_nonneg _))))

omit hB hk h hζ hH hp hs hL hℓ hM hv hy hZ he hJ hF hn h₁ h₂ N hq' hN U -- dangling J'
include he hF
open Tail
variable {ε:ℝ}
lemma blueParts {i:ℕ} (D: Target.Expense Q)(hx:Quotes.preExponent P'≤ D.earn)(hR:rise Q D L W μ s o P'.order P'.power l χ ε)(hS:Stamp T)(hK:i≤l+1)(hv : ∀ (p:H.fragrances) k,k ∈ F' p → i ≤ ranked H Y l p k) :
    shop H B q₁ Ra P' (fun i=> (WU) i (F' i)) (betaF G s L^requested i ε):= by
   let e₀:= D.one / 2; let a:=D.earn; let σ:=P'.order; let d:=P'.power
   obtain ⟨A,a',C,X',v₁,t',r,B',D',x',b,y,K,θ,ρ,w,l',n,hP,hFee,h⟩:= hR
   obtain ⟨N,hA,hB,hF'⟩:= h _ _ _ _ hS _ _ H; obtain ⟨N',hQ',hk⟩:= h _ _ _ _ hS _ _ J'
   let z' :ℝ:= l+1; have hz:0 ≤ z':=by unfold z'; positivity
   have hh₀:0<e₀:= half_pos D.first
   let α:= Grafting.teen N'.conduit hP.leg hz hQ' hFee N hA -- check
   obtain ⟨hℓ,hG,hr',hu,hH,hT,hτ,hM,hδ,hθ,hB',hv',hL⟩:= hP
   have ht (i):= show N'.conduit.goalsL i ≤ α.conduit.goalsL i from le_add_of_nonneg_left (N.conduit.uses.nonneg (.inr (.inl i))) -- le.left favors second? check
   have ha: LocalBookingsR2 z' (b+b) α.conduit:= Grafting.charters _ _ hℓ hz hA hQ' hFee -- pass
   have hhN p:= totalN (l:=l) H χ p hF' hB α hℓ hz hG hr' Y u hU
   let φ₀ i:= totalBill H χ i α Y u K D' θ z' x' ρ l
   have hX : Ready H.smallAt P'.B (fun i=>2^σ*φ₀ i) (a+e₀) w e₀ (1/2) :=by
      rw [hF]; refine ⟨hu,hh₀,hB',by norm_num,fun i=>mul_nonneg (by positivity) (hhN _),?_⟩
      have hp:a+e₀+e₀ ≤ Q.exp:=by unfold a e₀; linarith only [D.worth,D.second]
      exact fun i=>budget_loosen (incarnate H χ hF' hB α ha hℓ hz hG hr' Y u hU hδ hp i) hθ
   have hy' : Sailor G P'.threshold y σ:= by rw [he]; exact ⟨fun c u h=> N.weigh.stroke c _ (h.trans N.talent)⟩
   have h':= blueBooks H χ Y u hU B z l hF' hB α ha hℓ hz hG hr' hT hH hτ hM q₁ hQ hq Ra hr P' he le_rfl hF d le_rfl y N.income hy' N.near hh₀ hx F' wg ht hQ' hX i hv
   have h:= hv' i hK; unfold Tail.report at h; rw [one_mul] at h; exact opened H B q₁ Ra h' h
end YM.LocalTaylorR2.Orbit
