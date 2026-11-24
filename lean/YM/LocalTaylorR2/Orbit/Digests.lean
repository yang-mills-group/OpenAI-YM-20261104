import YM.LocalTaylorR2.Orbit.Casting
import YM.MergeProof.Magma
/-! Explicit template output at actual Support.Query. -/
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
open Ovens Photo Marlin
variable (ht: ∀ i,z i*z i=0)(h0:∀ i,(z i).part B.quiet=0) (R₀:Rep G c)
variable (K₀:ℝ → Finset ι→ Ovens.Code G c) {u₀ b₀ y' :ℝ} (hz:Photo.Usable Y H χ R₀ u K₀ e u₀ y')
    [Fintype Z] {u':H.fragrances→ Config G c→ Poly B} {P':BudgetPoint}

local notation "α"=> Photo.headSheet Y H χ u B z
abbrev cloaked (P:BudgetPoint)(f:H.fragrances→ Config G c→ Poly B) : H.fragrances→ Config G c→ Poly B:= fun i=> masked P.threshold (reachability i) (f i)
-- prove reassembly prices Towed for BOTH BEFORE composing masks B. Uniform geometric necessity. This file also imports exact `.Pays term` part.
omit [Fintype Z] in
lemma mask_parts (P:Support c) (S:ℝ) (u:Config G c→ Poly B)(i:B.Mode): (fun U=> (masked S P u U).part i)= masked S P (fun U=>(u U).part i):=by
   ext U; by_cases h: Healthy S P U <;> simp [h] -- test
omit [Fintype ι] [Fintype Z] in
lemma tooburn (F: Config G c → Poly B)(he:∀ i:B.Mode,P'.Regular (reachability k) (fun U=>(F U).part i))(hp:∀ U, GridApprox.Nil.Scoped {x| Ra x∈ (H.bookFoot (Sum.inr k))} (F U) ∧ (F U).part B.quiet=0):
    Burns Ra (reachability k) (masked P'.threshold (reachability k) F) P'.threshold:=by -- Z₀ typo; Fintype Z? Borne B expects? see.
  let P:= reachability k; let f i: Config G c→ ℂ:= fun U=>(F U).part i; let u:= masked P'.threshold P F
  have hh(i:B.Mode): (fun U=> (u U).part i)=masked P'.threshold P (f i):= mask_parts B _ _ _ _
  have hv(i:B.Mode): UsesFinal P'.threshold P (fun U=> (u U).part i) ∧ GaugeInvariant (fun U=> (u U).part i) :=by
     rw [hh]; constructor
     · intro U V hx hp; have hh:Healthy P'.threshold P U ↔ Healthy P'.threshold P V:= by unfold Healthy; rw [disjoint_iff_inter_eq_empty,disjoint_iff_inter_eq_empty,hp]
       unfold masked; simp only [Set.indicator,Set.mem_setOf_eq,hh,(show f i U=f i V from (he i).sites U V hx)]; rfl
     intro z U; unfold masked Healthy; simp only [Set.indicator,Set.mem_setOf_eq,gauge_flags,(show f i (gauge z U)=f i U from (he i).symmetry z U)]; split_ifs <;> rfl
  change Burns _ P u _
  have hu (U:Config G c)(hq:u U≠0): Healthy P'.threshold P U:= Classical.byContradiction (fun h=>hq (masked_ne _ _ _ _ h))
  refine {home:=fun U V h h'=>?_
          turns:=fun p V=>?_
          me:=fun i=>?_
          scope:=fun U=>?_
          sil:=fun U=>?_
          permits:=hu}
  · ext i:1; exact (hv i).1 U V h h'
  · ext i:1; exact (hv i).2 p V
  · rw [hh]; exact masked_measurable _ _ _ (he i).borel
  all_goals by_cases hx:u U=0
  · rw [hx]; exact fun _ _ =>rfl
  · unfold u; rw [masked_eq _ _ _ _ (hu U hx)]; exact (hp U).1
  · rw [hx]; rfl -- may simp
  unfold u; rw [masked_eq _ _ _ _ (hu U hx)]; exact (hp U).2
omit [Fintype ι] [Fintype Z] in
lemma choir_ready (h:shop H B q₁ Ra P' u' b₀): (∀ k:H.fragrances,Burns Ra (reachability k) (cloaked H B P' u' k) P'.threshold) ∧ Towed q₁ (reachability (H:=H)) (cloaked H B P' u') P'.B (Quotes.preExponent P') b₀:=by
  obtain ⟨f,hf,h,ht⟩:=h; constructor
  · intro k; obtain ⟨g,-,-,he,hp⟩:=ht k; exact tooburn H B k Ra (u' k) (fun i=>(he i).1) hp
  refine ⟨f,hf,h,?_⟩; intro i; obtain ⟨p,hp,hL,he,h⟩:= ht i; refine ⟨p,hp,?_,hL⟩
  intro U m; let P:=reachability i; unfold cloaked; by_cases hh:Healthy P'.threshold (reachability i) U
  · rw [masked_eq _ _ _ _ hh]; exact ((he m).2 (Song.locate H i).site (Song.locate H i).anchor).2 U hh [] (Nat.zero_le _) (by simp)
  rw [masked_ne _ _ _ _ hh,Poly.part_nil,norm_zero]; exact hp m
omit [Fintype ι] [Fintype Z] in
lemma opened (h: shop H B q₁ Ra P' u' b₀)(hx: b₀≤ e) : shop H B q₁ Ra P' u' e:=by obtain ⟨f,hf,h,ht⟩:=h; exact ⟨f,hf,fun i=>budget_loosen (h i) hx,ht⟩
include ht h0 hU in
omit [Fintype Z] in
lemma from_mask (hP:P'.threshold=Pressure.temp s): Photo.headSheet Y H χ u B z= cloaked H B P' (fun i=> measureS H χ Y u B z l i univ):=by
  funext k U; have hz:= awakened H χ Y u hU B z l k ht h0 U; rw [hz]; unfold cloaked; rw [hP]
-- full canonical read before `plus registration` (doesn't merge here -- retains frame attachment to THIS K)
abbrev refer (R:Rep G c)(f : H.fragrances→ Config G c→ Poly B)(F:ℕ→ Config G c→ Poly B)(V:Config G c):= (Real.exp (R.exponent V):ℂ) • (Poly.pass (∑' i,cloaked H B R.p f i V) * ∑' p,Photo.fronts R.activities (fun i=> F i V) V R.p p)
def inquiries (R:Rep G c)(F:ℕ→ Config G c→ Poly B)(x:ℝ): Prop := (∀ i:ℕ, MergeProof.Accent.Flow Ra (MergeProof.barcode R.activities i) (F i) R.p.threshold∧ ∀ U,(F i U).part B.quiet=(R.activities.K i U:ℂ) ∧ (F i U≠0 → (R.activities.forced i).eligible R.p.threshold U))∧ Towed q₁ (fun i=>(R.activities.forced i).support) F R.p.B (R.p.supportExponent+1) x
local notation "P₀"=> (fun i=> measureS H χ Y u B z l i univ)
include hz hQ hr hq ht h0
local notation "gb"=> Photo.Fleece K₀ B z
lemma auditedK (hw: Merge.Motion.Pays R₀.activities (Marlin.raiser R₀.p) K₀ b₀ (R₀.p.supportExponent+1)) : inquiries B q₁ Ra R₀ (gb) b₀ ∧ S.push R.beta (Photo.given (S:=S) Y u B z) = refer H B R₀ P₀ (gb) ∧ ∀ U:Config G c, Summable (Photo.fronts R₀.activities (fun i=>gb i U) U R₀.p):=by
   have hv:= hz.gas
   have hh : 0≤ R₀.p.supportExponent+1:= add_nonneg R₀.p.exponent_pos.le zero_le_one
   refine ⟨⟨fun i=> ?_,Photo.flag_K (P:=Marlin.raiser R₀.p) _ _ _ _ q₁ hQ hq hw hh⟩,funext (fun U=>?_),fun U=>?_⟩
   · obtain ⟨c,hc,hF⟩:=hv.bought
     refine ⟨Photo.river _ H χ _ _ K₀ B z hz Ra hr i,fun U=>?_⟩
     let f V (q:ℝ) (l:Finset ι) := K₀ q l i V
     constructor
     · change (sound z (f U)).part B.quiet=_; rw [Switch.sunset _ (hc i) z U h0] -- may using rfl
       rw [hv.term ∅]
     intro hU; refine freight (u:=f) U (fun p h => (hv.rear i p).2.2.2 U h) hU
   · unfold refer; rw [show cloaked H B R₀.p P₀= _ from (from_mask H χ Y u hz.vacuum B z l ht h0 hz.temp).symm]
     exact (Photo.acts Y H χ R₀ u K₀ _ z ht hz h0 U).symm -- notation unwinding
   exact (Photo.holds z ht R₀.activities K₀ hz.gas U).summable
end YM.LocalTaylorR2.Orbit
