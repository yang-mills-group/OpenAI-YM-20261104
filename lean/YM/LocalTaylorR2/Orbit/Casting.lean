import YM.LocalTaylorR2.Orbit.Gateway
import YM.MergeProof.Sate
/-! Coefficient-special budget to the ACTUAL Pack at Stope. Includes all Cipher.marker derivative loans. -/
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
def shop (p:BudgetPoint)(f:H.fragrances→ Config G c→Poly B)(v:ℝ):Prop:=
    ∃ g:H.fragrances→ℝ,Summable g∧ Ac.Hit (reachability (H:=H)) p.B g (Quotes.preExponent p) v ∧ ∀ i,∃ u:B.Mode→ℝ, 0≤u ∧ wordsPrice q₁ u≤g i ∧ (∀ m:B.Mode,p.Regular (reachability i) (fun U=> (f i U).part m) ∧ ∀ x∈ reachability i,p.supBounds x (reachability i) (fun U=>(f i U).part m) (u m)) ∧ ∀ U, GridApprox.Nil.Scoped {x| Ra x∈reachability i} (f i U) ∧ (f i U).part B.quiet=0
local notation "WU"=> measureS H χ Y u B z l
local notation "pr0"=> Quotes.preExponent P'
omit [Fintype Z] in -- does not use even ι
omit [Fintype ι] in
lemma hitsA (f:H.ThinP→ℝ)(h: Ready H.smallAt P'.B (fun i=>2^j*f i) (a+δ) wN δ (1/2))
    (r:ℕ)(hv:0<δ)(h2: pr0 ≤ a) (hw:1≤ρ) :
    Ac.Hit (reachability (H:=H)) P'.B (fun i=>(ρ^r)⁻¹ * allowance P' i j n' f) pr0 ((ρ^r)⁻¹*(collars G δ s j n'*(wN*(1-1/2:ℝ)⁻¹))):=by
    -- adapted from Corral
    let Z:=reachability (H:=H); intro x
    let u:= (ρ^r)⁻¹; have hu:0<u:=by unfold u; positivity
    have hp:0 ≤ shiftG s:=by unfold shiftG; positivity
    have hg i : 0≤f i:=nonneg_of_mul_nonneg_right (h.2.2.2.2.1 i) (by positivity : (0:ℝ)<2^j)
    have hK:0≤a+δ:= add_nonneg ((show (0:ℝ)≤AnalyticBridge.VerifiedReset.Quotes.preExponent P' from by unfold AnalyticBridge.VerifiedReset.Quotes.preExponent; have h:=P'.exponent_pos; positivity).trans h2) hv.le
    have hz:=Ursell.log_hit_tail _ _ _ H.testS h hK 0 x
    simp only [pow_zero,mul_one,Nat.zero_le,true_and] at hz
    let v:= collars G δ s j n'
    have ht:0≤v:=by unfold v collars Reserves.polyPrice; positivity
    have hh := budget_scale hu.le (budget_scale ht hz)
    refine budget_mono hh (fun z=>?_) fun z=> ?_
    · split
      next=>
        apply mul_nonneg _ (Real.exp_pos _).le; apply mul_nonneg hu.le; apply mul_nonneg (pow_nonneg (mul_nonneg hp _) _) (clusters_nonneg _ (fun i=>mul_nonneg (by positivity) (hg _)) _); positivity
      exact le_rfl
    split
    next hy=>
      have hV: x∈ Z _:=hy
      let τ:ℝ:=coverNumber P'.B (Z z)
      let Hq:= clusters H.seam (fun i=>2^j*f i) z.snd
      have hu':0≤Hq := clusters_nonneg _ (fun i=>mul_nonneg (by positivity) (hg _)) _
      have he':0≤τ:=Nat.cast_nonneg _
      rw [if_pos (show x∈unionOf H.smallAt z.2 from hV)]; change u*((shiftG s*(1+τ))^(j*n')*Hq) * Real.exp (_*τ) ≤ u*(v*(Hq*Real.exp ((a+δ)*τ)))
      unfold v collars
      rw [Nat.mul_comm j n',mul_pow,add_mul a, Real.exp_add]; have h := polynomial_cost hv he' (n'*j)
      apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (pow_nonneg hp _)) hu') hu.le) (Real.exp_pos _).le)
      unfold Reserves.polyPrice
      nlinarith only [mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h2 he')) (show 0≤u*(((shiftG s)^(n'*j)*(δ⁻¹^(n'*j)* ↑((n'*j).factorial) * Real.exp δ*Real.exp (δ*τ)))*Hq) by positivity)]
    exact hh.1 z
include hU h hr hQ hq hk U hB hζ hH hp hs hL hℓ hM he hJ hF hn hv hy hZ h₁ h₂
lemma shines (hY: Ready H.smallAt P'.B (fun i=>2^j* W₀ i) (a+δ) wN δ (1/2)) (r:ℕ)(hc:∀ i q,q∈F' i → r ≤ ranked H Y l i q): shop H B q₁ Ra P' (fun i=> WU i (F' i)) ((ρ^r)⁻¹*(collars G δ s j n'*(wN*(1-1/2:ℝ)⁻¹))) :=by
  have hr i:= retainsS H χ Y u B z l i _ hr (F' i)
  choose u hP ht hX using fun i=> refined H χ Y u hU B z l i hk U N hB h hζ hH hp hs hL hℓ hM q₁ hQ hq P' he hJ hF n' hn x' hy hv hZ (F' i) r (hc i)
  let f i:= (ρ^r)⁻¹*allowance P' i j n' W₀ -- local notation capture
  have hv:= hitsA H P' n' W₀ hY r h₁ h₂ hp
  have hf i:0≤f i:= (show 0≤ wordsPrice q₁ (u i) from sum_nonneg (fun j _=> mul_nonneg (Poly.worth hQ _).le (hP i j))).trans (ht i)
  refine ⟨f, ?_,hv,fun i=> ⟨_,hP i,ht i,hX i,hr i⟩⟩
  have hD : ∀ i:H.fragrances,(reachability i).Nonempty := fun i=> ⟨_,(Song.locate H i).anchor⟩
  have hf' := Product.everyone_ne _ _ hf (fun i _=> hD i) hv
  exact hf'.2.1.of_nonneg_of_le hf (fun i=> le_mul_of_one_le_right (hf i) (Real.one_le_exp (mul_nonneg (show 0 ≤pr0 from by unfold Quotes.preExponent; have h:= P'.exponent_pos; positivity) (Nat.cast_nonneg _))))
end YM.LocalTaylorR2.Orbit
