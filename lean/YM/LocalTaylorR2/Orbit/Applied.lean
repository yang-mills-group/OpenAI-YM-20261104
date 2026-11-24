import YM.LocalTaylorR2.Orbit.Banker
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
def apportion (k:H.fragrances)(X:ℕ→Prop):= univ.filter (fun i:Booking H Y l k=>X (ranked H Y l k i))
def sketch (Z:Bool)(i:H.fragrances):= WU i (apportion H Y l i (fun j=> if Z then ¬ l+1 ≤ j else l+1≤ j)) -- false error
abbrev fullS := fun i=> WU i univ
local notation "A!"=> fullS H χ Y u B z l
local notation "E!"=> sketch H χ Y u B z l
local notation "p!"=> (fun f U=>Poly.pass (∑' i,cloaked H B (B₀) f i U))
local notation "w!"=> Mallow.straw μ L G s
open Tail
structure Budgeted (ε v:ℝ) : Prop where
    stencil (g : ∀ k:H.fragrances, Finset (Booking H Y l k)) (i): i ≤ l+1 → (∀ j k,k∈g j→i ≤ ranked H Y l j k) → shop H B q₁ Ra (B₀) (fun i=> WU i (g i)) (betaF G s L^requested i ε)
    partition : A! = E! true+ E! false
    pass : shop H B q₁ Ra (B₀) (E! true) (betaF G s L^requested 0 ε)∧ shop H B q₁ Ra (B₀) (E! false) v
    hard : inquiries B q₁ Ra R₀ (Photo.Fleece K₀ B z) w! ∧ (Blush.glyph s)⁻¹*w! ≤ betaF G s L^ (-(l+1:ℝ))
    physical : let K:= Photo.Fleece K₀ B z; let v:= refer H B R₀ A! K; S.push R.beta (Photo.given (S:=S) Y u B z)=v ∧ ∀ U, Summable (Photo.fronts R₀.activities (fun i=> K i U) U R₀.p) ∧
      Summable (fun k=>cloaked H B R₀.p (A!) k U) ∧ v U = p! (E! false) U * refer H B R₀ (E! true) K U
include hQ in
omit [Fintype Z] in
private lemma traffic (f:H.fragrances→ Config G c→ Poly B) {x:ℝ} (h:shop H B q₁ Ra R₀.p f x)(U:Config G c): Summable (fun i=>cloaked H B (B₀) f i U) ∧ (∑' i,cloaked H B R₀.p f i U).part B.quiet=0:= by
   obtain ⟨hp,h⟩:= choir_ready H B q₁ Ra h
   have ht:= (Towed.repair h hQ U).2
   exact ⟨ht,(Poly.share ht _).trans (by simp only [(hp _).sil U, tsum_zero])⟩ -- simp_rw maybe
omit [Fintype Z] in
lemma part_doc : A! = E! true+ E! false:=by
   ext1 i; ext1 U; unfold fullS sketch apportion measureS; simp only [Pi.add_apply, Bool.false_eq_true,ite_false,ite_true]
   rw [add_comm (∑ i' ∈univ.filter (fun j=> ¬l+1≤ ranked H Y l i j), slice H χ Y u B z l i i' U) _]; exact (Finset.sum_filter_add_sum_filter_not ..).symm
include hq hr hQ h0 ht
variable {s' t v δ' : ℝ} (heU:Photo.Usable Y H χ R₀ u K₀ δ' e t)
    (hw:Merge.Motion.Pays R₀.activities (Marlin.raiser R₀.p) K₀ (Mallow.straw μ L G s) (R₀.p.supportExponent+1))
variable (Y₁ : Target.Expense Q) (he:Quotes.preExponent R₀.p≤ Y₁.earn)(hF:R₀.p.B=radiusB s)(hStamp:Stamp T)
include heU hw he hStamp hF
lemma charge_at (ε:ℝ)(hc:betaF G s L^requested (l+1) ε ≤ v)(hp: pledge Q Y₁ L W μ s o (B₀).order (B₀).power l χ ε):
    Budgeted H χ Y u B z l q₁ Ra R₀ K₀ ε v:=by
   let e₀:= Y₁.one / 2; let a:=Y₁.earn; let σ:=(B₀).order; let d:=(B₀).power
   obtain ⟨A,a',C,x,v₁,t',r,B',D,x',b,y,K,θ,ρ,w,l',n,hP,h⟩:= hp
   obtain ⟨N,hA,hB,hF'⟩:= h _ _ _ _ hStamp _ _ H
   let z' :ℝ:= l+1; have hz:0 ≤ z':=by unfold z'; positivity; -- remove ;
   have hh₀:0<e₀:= half_pos Y₁.first
   have hQ' := heU.vacuum
   obtain ⟨hℓ,hG,hr',hu,hH,hT,hτ,hx,hδ,hθ,hB',hv,hL⟩:= hP
   have hhN p:= totalN (l:=l) H χ p hF' hB N hℓ hz hG hr' Y u hQ'
   let φ₀ i:= totalBill H χ i N Y u K D θ z' x' ρ l
   have hX : Ready H.smallAt (B₀).B (fun i=>2^σ*φ₀ i) (a+e₀) w e₀ (1/2) :=by
      rw [hF]; refine ⟨hu,hh₀,hB',by norm_num,fun i=>mul_nonneg (by positivity) (hhN _),?_⟩
      have hp:a+e₀+e₀ ≤ Q.exp:=by unfold a e₀; linarith only [Y₁.worth,Y₁.second]
      exact fun i=>budget_loosen (incarnate H χ hF' hB N hA hℓ hz hG hr' Y u hQ' hδ hp i) hθ
   have hv (g : ∀ k:H.fragrances, Finset (Booking H Y l k)) (i:ℕ) (hx:i ≤ l+1) (hY:∀ j k,k∈g j→i ≤ ranked H Y l j k) : shop H B q₁ Ra (B₀) (fun i=> WU i (g i)) (betaF G s L^requested i ε):=by -- HX notation k capture
     have hR : Sailor G (B₀).threshold y (B₀).order:=by rw [heU.temp]; exact ⟨fun c u h=> N.weigh.stroke c _ (h.trans N.talent)⟩
     have hp:= shines H χ Y u hQ' B z l hF' hB N hA hℓ hz hG hr' hT hH hτ ‹betaF G s L^(l+1:ℝ) ≤ Real.exp (Q.mark L μ s)› q₁ hQ hq Ra hr (B₀) heU.temp le_rfl hF d le_rfl y N.income hR N.near hh₀ he g hX i hY -- args
     have h:= hv i hx; unfold Tail.report at h; rw [one_mul] at h; exact opened H B q₁ Ra hp h
   have hM:= hv (fun i=> apportion H Y l i (fun j=> if true=true then ¬ l+1 ≤ j else l+1≤j)) 0 (Nat.zero_le _) (fun i j hx=> Nat.zero_le _) -- ite Decidable; notation
   let Y₀:= (E! true); let Y₂:= (E! false)
   have hT: shop H B q₁ Ra (B₀) Y₂ v:=by
     refine opened H B q₁ Ra (hv _ (l+1) le_rfl ?_) hc; intro i j hp
     have hx:= show j ∈ apportion H Y l i (fun t=>if false=true then ¬ l+1 ≤ t else l+1 ≤ t) from hp; simpa [apportion] using hx
   have hS : shop H B q₁ Ra (B₀) Y₀ _:= show shop H B q₁ Ra (B₀) Y₀ (betaF G s L^requested 0 ε) from hM
   have hA':shop H B q₁ Ra (B₀) (A!) _:= hv (fun _=>univ) 0 (Nat.zero_le _) (fun i j hp=> Nat.zero_le _)
   obtain ⟨hz,hx,hF⟩:= auditedK H χ Y u B z l q₁ hQ hq Ra hr ht h0 R₀ K₀ heU hw
   have hP := part_doc H χ Y u B z l
   refine ⟨hv,hP,⟨hS,hT⟩,⟨hz,hL⟩,?_⟩; intro k' u₀
   refine ⟨hx,fun U=> ?_⟩
   obtain ⟨hU,ha'⟩:= traffic H B q₁ hQ Ra _ _ hA' U; obtain ⟨hV₀,hx'⟩:= traffic H B q₁ hQ Ra _ _ hS U; obtain ⟨hV₂,hz'⟩:=traffic H B q₁ hQ Ra _ _ hT U
   refine ⟨hF U,hU,?_⟩
   let H' :=cloaked H B (B₀); let F f:= ∑' i,H' f i U
   have he:F (A!)=F Y₂+F Y₀:=by
     rw [← Summable.tsum_add hV₂ hV₀]; refine tsum_congr (fun i=>?_); change masked _ (reachability i) (A! i) U = masked _ (reachability i) (Y₂ i) U + masked _ (reachability i) (Y₀ i) U; rw [hP]; by_cases hp0: Healthy (B₀).threshold (reachability i) U
     · rw [masked_eq _ _ _ _ hp0,masked_eq _ _ _ _ hp0,masked_eq _ _ _ _ hp0]; exact add_comm ..
     rw [masked_ne _ _ _ _ hp0,masked_ne _ _ _ _ hp0,masked_ne _ _ _ _ hp0,add_zero]
   unfold u₀ refer; change _ • (Poly.pass (F (A!))*_) = Poly.pass (F Y₂) * (_ • (Poly.pass (F Y₀)*_))
   rw [he,Extra.Trajectories.pass_add hz' hx', mul_smul_comm]; rw [mul_assoc]
end YM.LocalTaylorR2.Orbit
