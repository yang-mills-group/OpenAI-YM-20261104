import YM.LocalTaylorR2.Copper.Chef
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
omit [Fintype ι] [Fintype Z] in
lemma privatize (A' B':Copper.Stems T) :
   let f : ∀ k:H.fragrances, Finset (Booking H Y l k):= fun i=> (F' i).filter (fun p=> 1 ≤ ranked H Y l i p)
   let W:= answering H χ Y u B z l; W F' A'- W F' B'=W f A'-W f B':=by
   intro F W'; let U (k:H.fragrances):=(F' k).filter (fun q=> ¬1≤ ranked H Y l k q)
   have h (V'):W' F' V'= W' F V'+ W' U V':= by ext1 i; ext1 X; exact (Finset.sum_filter_add_sum_filter_not ..).symm
   have hz : W' U A'= W' U B':=by
      ext1 i; ext1 X; unfold W' answering cameoS; apply sum_congr rfl; intro j hj; have ht:= (mem_filter.mp hj).2; unfold cameoSlice; refine congr_arg (fun G:ℝ=>((coeff H i*G:ℝ):ℂ) • petition H Y B z l i j) (?_: cameoC H χ Y u l i A' j X=cameoC H χ Y u l i B' j X)
      apply prod_congr rfl; intro k hk
      have hy:(j k).2.val ≤ ranked H Y l i j:=single_le_sum (f:=fun k=> (j k).2.val) (fun _ _=> Nat.zero_le _) hk
      have he : (j k).2=0:= Fin.ext (by change _=0; omega); unfold wiredBox; rw [he]; unfold stock stemPlug; split; swap; · rfl
      split; swap; · rfl
      apply congr_arg (turnWeight Y u (j k).1 * ·); unfold convolve; apply Finset.sum_congr rfl; intro p hp; dsimp only; have hP:= mem_filter.mp hp|>.2; unfold flowerCup; simp_rw [Copper.namesZero A' _ hP,Copper.namesZero B' _ hP]
   rw [h,h,hz]; abel
local notation "β"=> betaF G s L
variable (J':Cash W s μ L Q o C T (Reel.bend R wg)){ε:ℝ}
include he hF hU hr hQ hq J'
open Tail
lemma steel {i:ℕ} (D: Target.Expense Q)(Ξ:King.Engine G)(hx:Quotes.preExponent P'≤ D.earn)(hR:Orbit.royalty Ξ Q D L W μ s o P'.order P'.power l χ ε)(hS:Stamp T)(hK:i≤l+1)(hv : ∀ (p:H.fragrances) k,k ∈ F' p → i ≤ ranked H Y l p k) :
    shop H B q₁ Ra P' (answering H χ Y u B z l F' (Ξ.plug H wg l)) (β^requested i (ε/2)) ∧
     ((∀ (p:H.fragrances) k,k∈ F' p→ ranked H Y l p k ≤ l) → shop H B q₁ Ra P' (chef H χ Y u B z l F' wg-answering H χ Y u B z l F' (Ξ.plug H wg l)) (β^requested (l+1) ε)):= by
   let e₀:= D.one / 2; let a:=D.earn; let σ:=P'.order; let d:=P'.power
   obtain ⟨A,a',C,X',v₁,t',r,B',D',x',b,y,K,θ,ρ,w,l',n,hP,hFee,hwg,h⟩:= hR
   obtain ⟨N,hA,hB,hM,hF'⟩:= h _ _ _ _ hS _ _ H; obtain ⟨N',hQ',hα,hΞ',hZ₂⟩:= h _ _ _ _ hS _ _ J'
   let z' :ℝ:= l+1; have hz:0 ≤ z':=by unfold z'; positivity
   have hh₀:0<e₀:= half_pos D.first
   obtain ⟨hℓ,hG,hr',hu,hH,hT,hτ,hM,hδ,hθ,hB',hv',hL⟩:= hP
   have hK':= (le_add_of_nonneg_right (budget_nonneg (hQ'.leases.hit 0))).trans hFee
   let α':= Grafting.teen N'.conduit hℓ hz hQ' hK' N hA
   have ha: LocalBookingsR2 z' (b+b) α'.conduit:= Grafting.charters _ _ hℓ hz hA hQ' hK'
   let α:= Grafting.teen N'.conduit hℓ hz hQ' hFee α' ha
   have ha: LocalBookingsR2 z' (b+b+b) α.conduit:= Grafting.charters _ _ hℓ hz ha hQ' hFee
   have ht (i): N'.conduit.goalsL i + N'.conduit.goalsL i ≤ α.conduit.goalsL i := add_le_add_left (le_add_of_nonneg_left (N.conduit.uses.nonneg (.inr (.inl i)))) _
   have hhN p:= totalN (l:=l) H χ p hF' hB α hℓ hz hG hr' Y u hU
   let φ₀ i:= totalBill H χ i α Y u K D' θ z' x' ρ l
   have hX : Ready H.smallAt P'.B (fun i=>2^σ*φ₀ i) (a+e₀) w e₀ (1/2) :=by
      rw [hF]; refine ⟨hu,hh₀,hB',by norm_num,fun i=>mul_nonneg (by positivity) (hhN _),?_⟩
      have hp:a+e₀+e₀ ≤ Q.exp:=by unfold a e₀; linarith only [D.worth,D.second]
      exact fun i=>budget_loosen (incarnate H χ hF' hB α ha hℓ hz hG hr' Y u hU hδ hp i) hθ
   have hy' : Sailor G P'.threshold y σ:= by rw [he]; exact ⟨fun c u h=> N.weigh.stroke c _ (h.trans N.talent)⟩
   let Φ i:= Copper.contour H wg l (Reel.Strand.dial i*ρ^l) Ξ; let Zq:= answering H χ Y u B z l
   have hP (F': ∀ k:H.fragrances, Finset (Booking H Y l k))(p:Reel.Strand)(i:ℕ)(hK:i≤l+1)(hv : ∀ (p:H.fragrances) k,k ∈ F' p → i ≤ ranked H Y l p k) : shop H B q₁ Ra P' (Zq F' (Φ p)) (β^requested i (ε/2)):=by
     have h':= cameoBooks H χ Y u hU B z l hF' hB α ha hℓ hz hG hr' hT hH hτ hM q₁ hQ hq Ra hr P' he le_rfl hF d le_rfl y N.income hy' N.near hh₀ hx F' (Φ p) (Copper.guides Ξ hΞ' hr' ht hQ' p) hX i hv
     have h:= hv' i hK; unfold Tail.report at h; rw [one_mul] at h; exact opened H B q₁ Ra h' h
   have hz: 0<ρ:= zero_lt_one.trans_le hr'; let η:ℝ:=(ρ^l)⁻¹; have hη:0≤η:=by unfold η; positivity
   let z': Reel.Strand:= ⟨η,⟨by linarith,inv_le_one_of_one_le₀ (one_le_pow₀ hr')⟩⟩
   have hm: Φ z'=Ξ.plug H wg l:=by unfold Φ; rw [show Reel.Strand.dial z'*ρ^l=1 from inv_mul_cancel₀ (pow_ne_zero _ hz.ne'),Copper.knotTop]
   have hp: Φ Reel.Strand.bud= Reel.sprout H wg:=by unfold Φ; rw [show Reel.Strand.dial Reel.Strand.bud*ρ^l=0 from zero_mul _,Copper.knotCold]
   rw [← hm,show chef H χ Y u B z l F' wg=Zq F' (Φ Reel.Strand.bud) from by rw [hp]; rfl]; refine ⟨hP _ _ _ hK hv, fun hf=>?_⟩
   let X₁(i:H.fragrances):=(F' i).filter (fun p=> 1≤ ranked H Y l i p); let Y₀:= fun k=> Zq X₁ (Φ k)
   have heq : Zq F' (Φ Reel.Strand.bud)-Zq F' (Φ z')=Y₀ Reel.Strand.bud-Y₀ z':= privatize H χ Y u B z l F' (Φ Reel.Strand.bud) (Φ z')
   change shop _ _ _ _ _ (Zq F' (Φ Reel.Strand.bud)-Zq F' (Φ z')) _; rw [heq]
   have ht:= pennantG H B l q₁ Ra z' Y₀ (fun p=> hP X₁ p 1 (by omega) (fun i j hj=> (mem_filter.mp hj).2)) (fun i U hu m=> swifter H χ Y u B z l i α (fun i j hh=>hf i j (Finset.filter_subset _ _ hh)) Φ (Copper.romps (H:=H) Ξ hΞ') m U (he ▸ hu)) hη
   have hx:= shopScale H B q₁ Ra ht (-1); rw [norm_neg, norm_one, one_mul,neg_one_smul,neg_sub] at hx; exact opened H B q₁ Ra hx hwg
end YM.LocalTaylorR2.Orbit
