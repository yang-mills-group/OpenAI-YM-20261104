import YM.LocalTaylorR2.Sails.Bonny
import YM.LocalTaylorR2.Marigold.Wire
import YM.LocalTaylorR2.Marker.Sigil
import YM.LocalTaylorR2.Copper.Flat
import YM.LocalTaylorR2.Marigold.Portico
/-!
 # Price single Mark: post-K
 Uses from Daisy.Clutch.central. Signs untouched, inventory projected only once.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Marker
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Leaf R) (X:Coat T F) (H:Cash W x μ L Q o C T R)
    {Z : Support c} {k k':Finset ℕ}{u v : Air f G}

local notation "i₀" => M.turn.badge S
open Port Charge
open Reserves Tender Gas Ursell Trees Mixed
variable {j k n l : ℕ} {v₀ r d A D x' C' ζ η c' y: ℝ} {χ : Chi} (Ξ:Utopia H j v₀ d r C' χ)
open Candle Daisy.Charity
open scoped Classical
variable {k l:ℕ} (p:H.ThinP)
variable {b D K B v r w q' θ c' ρ ζ : ℝ} (N:Captain H j C' d v w A b r B q' (n+j) χ) (U:StoresR2 H j v d A D k x' n χ)(hr:Tinted G x K d o.a L χ j)
set_option quotPrecheck false
local notation "Z"=>N.conduit
local notation "d0"=> jewelDebt M Q L x

variable {ψ: Copper.Stems T}
local notation "K!" => refund M Q L x y
variable (h : 1≤betaF G x L) (hζ:0≤ζ) (hp:1≤ρ) (hy:1≤y) (hI:LocalBookingsR2 ζ c' N.conduit) (hY:Herd H N.conduit A B (n+j)) (hθ:1≤θ)(he:Charge.Allows l j θ)
    (hs:ρ*c'≤1) (hq: ρ^(l+1) ≤ betaF G x L^ζ) (hh:betaF G x L^ζ ≤ Real.exp (Q.mark L μ x))

-- new locus: must require *actual membership* in low rank before claiming. No eligibility checks by projection. cap `dream` on perch in proof, read original only where entitled.
variable (hξ:∀ i, Port.Burst H (H.supportP (identityLog i)) (ψ i))
include hξ
lemma amplify (q:Paint p.val l)(hp:chooseSlot q ≠ Candle.perch l) : Port.Burst H (H.smallAt p) (Copper.namesP ψ q) := by rw [Orbit.namesCol q hp]; exact Exponent.glow H ψ q _ (Subset.refl _) (fun _ _=> hξ _)
lemma vexS (h:treads M H p)(q:Paint (partners M p.val) l)(hp: chooseSlot q ≠ Candle.perch l) : Port.Burst H (H.smallAt p) (betide M H p ψ q):= by unfold betide; rw [Orbit.namesCol q hp]; exact ((Port.Burst.fat (stemTest M H)).mono (sees_set M H h)).times (Exponent.glow H ψ q _ (enough M H) (fun _ _=> hξ _))
lemma supineS (q:Orders l)(h0:q ≠ Candle.perch l): Items H p (dream M H p χ ψ q):=by
   by_cases hv:lush M H p; swap; · unfold dream; simp_rw [if_neg hv]; exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _=>rfl⟩
   unfold dream convolve; simp_rw [if_pos hv]; have hm (q₁:Paint (partners M p.val) l)(hh:chooseSlot q₁=q):= episodeSitesBurst (p:=p.val) H (vexS M H p hξ hv.1 q₁ (ne_of_eq_of_ne hh h0)) χ
   exact ⟨fun U V=> Finset.sum_congr rfl (fun i hi=> (hm i (mem_filter.mp hi).2).2.2 U V),Finset.measurable_fun_sum _ (fun i hi=> (hm i (mem_filter.mp hi).2).1), fun U V h=> Finset.sum_congr rfl (fun i hi=> (hm i (mem_filter.mp hi).2).2.1 _ _ h)⟩
lemma mercurialS (q:Orders l)(h0:q ≠ Candle.perch l): Items H p (mintC H χ ψ p q):=by
   by_cases hv:live H p; swap; · unfold mintC; simp_rw [if_neg hv]; exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _=>rfl⟩
   unfold mintC convolve; simp_rw [if_pos hv]; have hm (q₁:Paint p.val l)(hh:chooseSlot q₁=q):= episodeSitesBurst (p:=p.val) H (amplify H p hξ q₁ (ne_of_eq_of_ne hh h0)) χ
   exact ⟨fun U V=> Finset.sum_congr rfl (fun i hi=> (hm i (mem_filter.mp hi).2).2.2 U V),Finset.measurable_fun_sum _ (fun i hi=> (hm i (mem_filter.mp hi).2).1), fun U V h=> Finset.sum_congr rfl (fun i hi=> (hm i (mem_filter.mp hi).2).2.1 _ _ h)⟩

omit hξ
variable {Icy:ℝ}(ht:1≤Icy)(hT:Exponent.Bank H j k n x' l m Icy)(hF: Exponent.Lodestar H m Icy N.conduit ψ)
include hθ ht hF hr
lemma plotJet (q:Paint (partners M p.val) l)(hv:chooseSlot q ≠ Candle.perch l)(h0:treads M H p): Exponent.Rates H (H.unionP p.val) j m l Icy v d χ (betide M H p ψ q) (M.weight*Tender.forge N.conduit θ q) (speedS K r l*(1+H.shapeW p.val)):=by
  unfold betide; rw [Orbit.namesCol q hv]; intro E _ _ _ F X V u z x' w hX hW hΨ hχ hm hu
  have h:= Exponent.Rates.times H (Exponent.Rates.era H _ Icy m (v:=v) (markedSees M H hr)) (Exponent.tall H ψ hF ht q (p.val) (Finset.erase_subset ..) h0.1.2 (show inserts q ≤ l from by by_contra hk; exact hv (Fin.ext (min_eq_left (Nat.lt_of_not_ge hk)))) hθ) E F X V u z x' w hX hW hΨ hχ hm hu
  rw [zero_add] at h; apply h.climb le_rfl ?_
  let f i:= spanW T R (radiusB x) Q.halo i
  have hs : f (i₀) ≤ 2*H.shapeW p.val:= (Finset.single_le_sum (s:=p.val) (fun i _=> show 0≤f i from ?_) h0.2).trans (Utopia.worthy _ h0.1.2)
  · unfold speedS; nlinarith only [mul_le_mul_of_nonneg_left hs hr.salt,hr.salt]
  rcases i with i|i; exact zero_le_one; exact add_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
include hy U hT
lemma lavenderS (q:Orders l)(hz:q ≠ Candle.perch l) (V:Config G c) (hv: Healthy (Pressure.temp x) (H.smallAt p) V): Ore V (dream M H p χ ψ q) v ((K!)*period M H p N x' D K y θ q) j:=by
  unfold period; have hl:0< y:=zero_lt_one.trans_le hy
  split
  next h0=>
    let f q:= episode H χ p.val (betide M H p (l:=l) ψ q)
    have hk: (K!)*(y*jewel M Q L x)=M.weight:=by rw [(dew M H).2.2]; unfold refund; field_simp
    have hh(q':Paint (partners M p.val) l)(hq:chooseSlot q' ≠ Candle.perch l): Ore V (f q') v ((K!)*toll M H p N q' x' D K y θ) j:=by
      have hm : 0≤ speedS K r l:= by unfold speedS; have h:=hr.salt; have hb:=N.conduit.active; positivity
      have he:= Exponent.Rates.elans H hT U (plotJet M H p N hr hθ ht hF q' hq h0.1) ht (mul_nonneg M.profit (forgeN N.conduit hθ q')) hm
      unfold toll; rw [← mul_assoc (K!),← mul_assoc (K!),← mul_assoc (K!),hk]
      exact episodeCostBurst H N.oboe p.2.2 (vexS M H p hF.love h0.1 q' hq) he V hv
    intro E _ _ _ W s hw hW; unfold dream convolve; simp_rw [if_pos h0,Finset.mul_sum]; exact Brush.spree _ (fun p v=> f p (W v)) _ zero_le_one fun i hi=> hh i (ne_of_eq_of_ne (mem_filter.mp hi).2 hz) E W s hw hW
  next hF=> 
    have he : 0 ≤ period M H p N x' D K y θ q:= periodN M H p N hy _ hθ hr (zero_le_one.trans U.sure) U.fuel
    unfold period at he; rw [if_neg hF] at he; intro E _ _ _ W s hw hW; apply Brush.zi (Eventually.of_forall (fun i=> if_neg hF)) (mul_nonneg (div_nonneg (dew M H|>.2.1) hl.le) he) zero_le_one
omit hy hr in
lemma beelineS (q:Orders l)(hK:q≠ Candle.perch l) (V:Config G c) (hv:Healthy (Pressure.temp x) (H.smallAt p) V): Ore V (mintC H χ ψ p q) v (Price.schemePrice N D x' θ p q) j:= by
  by_cases hf:live H p; swap
  · intro E _ _ _ W s hw hW; apply Brush.zi (Eventually.of_forall (fun i=> if_neg hf)) (Price.positional N U hθ p q) zero_le_one
  have hh(p':Paint p.val l)(hΩ:chooseSlot p'≠ Candle.perch l): Ore V (episode H χ p.val (Copper.namesP ψ p')) v (Price.fare N x' D θ p.val p') j:= by
      have hb:0≤2*r*(l+3:ℝ):=by have hq:=(Z).active; positivity
      have h : Exponent.Rates H (H.unionP p.val) j m l Icy v d χ (Copper.namesP ψ p') (Tender.forge (Z) θ p') (2*r*(l+3:ℝ)*(1+H.shapeW p.val)):= by rw [Orbit.namesCol p' hΩ]; exact Exponent.tall H ψ hF ht p' p.val (Subset.refl _) hf.1.2 (show inserts p' ≤ l from by by_contra hk; exact hΩ (Fin.ext (min_eq_left (Nat.lt_of_not_ge hk)))) hθ
      have hw:= Exponent.Rates.elans H hT U h ht (forgeN (Z) hθ p') hb
      exact episodeCostBurst H N.oboe p.2.2 (amplify H p hF.love p' hΩ) hw V hv
  intro E _ _ _ W s hw hW; unfold mintC Price.schemePrice; simp_rw [if_pos hf]; exact Brush.spree _ (fun q v=> episode H χ p.val (Copper.namesP ψ q) (W v)) _ zero_le_one fun i hi=> hh i (ne_of_eq_of_ne (mem_filter.mp hi).2 hK) E W s hw hW
end YM.LocalTaylorR2.Marker
