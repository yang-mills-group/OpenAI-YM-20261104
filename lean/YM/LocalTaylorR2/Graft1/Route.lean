import YM.LocalTaylorR2.Marker.Sigil
import YM.LocalTaylorR2.Graft1.Pocket
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

variable {ψ: Reel.Scroll G f}{J:Cash W x μ L Q o C T (Reel.bend R ψ)}
local notation "K!" => refund M Q L x y
variable (h : 1≤betaF G x L) (hζ:0≤ζ) (hp:1≤ρ) (hy:1≤y) (hI:LocalBookingsR2 ζ c' N.conduit) (hY:Herd H N.conduit A B (n+j)) (hθ:1≤θ)(he:Charge.Allows l j θ)
    (hs:ρ*c'≤1) (hq: ρ^(l+1) ≤ betaF G x L^ζ) (hh:betaF G x L^ζ ≤ Real.exp (Q.mark L μ x))

abbrev nodule (ψ:Reel.Scroll G f) {l:ℕ}(q:Paint (partners M p.val) l):Port.Test T := fun F X u=> stems M H F X u*Reel.press H ψ q F X u
def dollop (χ:Chi)(ψ:Reel.Scroll G f)(q:Orders l)(U:Config G c):ℝ:= if lush M H p then convolve (U:=partners M p.val) q (fun i=> episode H χ p.val (nodule M H p ψ i) U) else 0
lemma real1 (χ:Chi) (q:Orders l)(hz:q.val≤ l): dollop M H p χ R.activities.E q=dial M H χ p q:=by
  have hk:q≠perch l:= by intro h; rw [h] at hz; change l+1 ≤ l at hz; omega
  funext v; rw [dial,if_neg hk]; rfl
include J
lemma keptM (h:treads M H p)(q:Paint (partners M p.val) l): Kept H (H.smallAt p) (nodule M H p ψ q):= ((stemTest M H).mono (sees_set M H h)).times (Orbit.holdsP H p J q (Finset.erase_subset ..))
lemma premium (q:Orders l): Items H p (dollop M H p χ ψ q):=by
   by_cases hv:lush M H p; swap; · unfold dollop; simp_rw [if_neg hv]; exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _=>rfl⟩
   unfold dollop convolve; simp_rw [if_pos hv]; have hm (q:Paint (partners M p.val) l):= episodeSites (p:=p.val) H (keptM M H p (J:=J) hv.1 q) χ
   exact ⟨fun U V=> Finset.sum_congr rfl (fun i _=> (hm i).2.2 U V),Finset.measurable_fun_sum _ (fun i _=> (hm i).1), fun U V h=> Finset.sum_congr rfl (fun i _=> (hm i).2.1 _ _ h)⟩
lemma premium' (q:Orders l): Items H p (Reel.team H (χ:=χ) ψ p q):=by
   by_cases hv:live H p; swap; · unfold Reel.team; simp_rw [if_neg hv]; exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _=>rfl⟩
   unfold Reel.team convolve; simp_rw [if_pos hv]; have hm (q:Paint p.val l):= episodeSites (p:=p.val) H (Orbit.holdsP H p J q (Subset.refl _)) χ
   exact ⟨fun U V=> Finset.sum_congr rfl (fun i _=> (hm i).2.2 U V),Finset.measurable_fun_sum _ (fun i _=> (hm i).1), fun U V h=> Finset.sum_congr rfl (fun i _=> (hm i).2.1 _ _ h)⟩
variable {ξ: Utopia J j v d r C' χ}{y₀:ℝ} (hF:∀ i,ξ.goalsL i≤ N.conduit.goalsL i)(hA:LocalBookingsR2 ζ y₀ ξ)
include hF hA h hζ hp hI hr hθ he hs
lemma seesM (hq:Paint (partners M p.val) l)(h0:treads M H p): Sees H j v d χ (nodule M H p ψ hq) (M.weight*Tender.forge N.conduit θ hq) (speedS K r l*(1+H.shapeW p.val)):=by
  have ht:c'≤1:=(le_mul_of_one_le_left (budget_nonneg (hI.leases.hit 0)) hp).trans hs; have hμ:= markedSees M H hr (v₀:=v)
  refine Sees.climb H (Sees.times H hμ (Orbit.blueSpeed H χ p _ _ hA hθ hq (Finset.erase_subset ..) h0.1 he hF (slack _ hI h hζ ht))) le_rfl ?_
  let f i:= spanW T R (radiusB x) Q.halo i
  have hs : f (i₀) ≤ 2*H.shapeW p.val:= (Finset.single_le_sum (s:=p.val) (fun i _=> show 0≤f i from ?_) h0.2).trans (Utopia.worthy _ h0.1.2)
  · unfold speedS; nlinarith only [mul_le_mul_of_nonneg_left hs hr.salt,hr.salt]
  rcases i with i|i; exact zero_le_one; exact add_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
include hy U
lemma pay1 (q:Orders l) (V:Config G c) (hv: Healthy (Pressure.temp x) (H.smallAt p) V): Ore V (dollop M H p χ ψ q) v ((K!)*period M H p N x' D K y θ q) j:=by
  unfold period; have hl:0< y:=zero_lt_one.trans_le hy
  split
  next h0=>
    have ht:c'≤1:=(le_mul_of_one_le_left (budget_nonneg (hI.leases.hit 0)) hp).trans hs
    let f q:= episode H χ p.val (nodule M H p (l:=l) ψ q)
    have hk: (K!)*(y*jewel M Q L x)=M.weight:=by rw [(dew M H).2.2]; unfold refund; field_simp
    have hh(q':Paint (partners M p.val) l): Ore V (f q') v ((K!)*toll M H p N q' x' D K y θ) j:=by
      have hm : 0≤ speedS K r l:= by unfold speedS; have h:=hr.salt; have hb:=N.conduit.active; positivity
      have hq:= Charge.holds U _ (mul_nonneg M.profit (forgeN N.conduit hθ q')) hm _ (seesM M H p N hr h hζ hp hI hθ he hs hF hA q' h0.1)
      unfold toll; rw [← mul_assoc (K!),← mul_assoc (K!),← mul_assoc (K!),hk]
      exact episodeCost H N.oboe p.2.2 (keptM M H p (J:=J) h0.1 q') hq V hv
    intro E _ _ _ W s hw hW; unfold dollop convolve; simp_rw [if_pos h0,Finset.mul_sum]; exact Brush.spree _ (fun p v=> f p (W v)) _ zero_le_one fun i _=> hh i E W s hw hW
  next hF=> 
    have he : 0 ≤ period M H p N x' D K y θ q:= periodN M H p N hy _ hθ hr (zero_le_one.trans U.sure) U.fuel
    unfold period at he; rw [if_neg hF] at he; intro E _ _ _ W s hw hW; apply Brush.zi (Eventually.of_forall (fun i=> if_neg hF)) (mul_nonneg (div_nonneg (dew M H|>.2.1) hl.le) he) zero_le_one
omit hy hr in
lemma pay' (q:Orders l) (V:Config G c) (hv:Healthy (Pressure.temp x) (H.smallAt p) V): Ore V (Reel.team H (χ:=χ) ψ p q) v (Price.schemePrice N D x' θ p q) j:= by
  by_cases hf:live H p; swap
  · intro E _ _ _ W s hw hW; apply Brush.zi (Eventually.of_forall (fun i=> if_neg hf)) (Price.positional N U hθ p q) zero_le_one
  have ht:c'≤1:=(le_mul_of_one_le_left (budget_nonneg (hI.leases.hit 0)) hp).trans hs
  have hh(p':Paint p.val l): Ore V (episode H χ p.val (Reel.press H ψ p')) v (Price.fare N x' D θ p.val p') j:= by
      have hb:0≤2*r*(l+3:ℝ):=by have hq:=(Z).active; positivity
      have hw:= holds U _ (forgeN (Z) hθ p') hb _ (Orbit.blueSpeed H χ p _ _ hA hθ p' (Subset.refl _) hf.1 he hF (slack _ hI h hζ ht))
      exact episodeCost H N.oboe p.2.2 (Orbit.holdsP H p J p' (Subset.refl _)) hw V hv
  intro E _ _ _ W s hw hW; unfold Reel.team Price.schemePrice; simp_rw [if_pos hf]; exact Brush.spree _ (fun q v=> episode H χ p.val (Reel.press H ψ q) (W v)) _ zero_le_one fun i _=> hh i E W s hw hW
end YM.LocalTaylorR2.Marker
