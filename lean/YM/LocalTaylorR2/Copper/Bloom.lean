import YM.LocalTaylorR2.Copper.Mingle
/-! Use ANY admissible E (through vacuum reading interpolation permits); test SEES only on that real clock.  Price for a real Crew on track alphabet. -/
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
open Marker Charge
local notation "HG"=> H.unionP Θ
local notation "T₀"=> restP M H p
variable {j l k n:ℕ} {D K e v₀ d r z x b' A :ℝ}
variable (Ξ:Utopia H j v₀ d r b' χ) (ht: Tinted G s K d o.a L χ j) (U:StoresR2 H j v₀ d A D k x n χ)
variable (hc:Orbit.checked M H p)
open Reserves Tender
local notation "V"=> Paint (T₀)
local notation "Ψ"=> Orbit.checked M H p ∧ Clear T₀ -- note local notation precedence (parenthesize)
local notation "K'"=> deck M H χ p
/- No need for generating a Leaf at the shadow state. Uses the actual Crew BEFORE evaluating partners. And the real peso for Kept/Stained tests. `turn.blank` only includes in the real H. Hence this applies to ALL dispatched marker programs in spite of the E interpolation. -/
open Copper
variable {uP:Copper.Stems T}
abbrev flowerCup (φ:Copper.Stems T)(q:V l):Port.Test T:= fun _ X u=> M.paidU X o.a (worldZ X R.beta u)* Copper.namesP φ q _ X u
abbrev stemPlug (φ:Copper.Stems T)(q:Orders l) (U:Config G c):= if Ψ then convolve (U:=T₀) q (fun k=> episode H χ Θ (flowerCup M H p φ k) U) else 0
def stock (φ:Copper.Stems T)(q:Orders l)(U:Config G c):ℝ:=if q≠perch l then stemPlug M H χ p φ q U else 0
lemma stock_off (φ:Copper.Stems T)(q:Orders l)(h:¬ (Ψ)): stock M H χ p φ q=fun _=>0:=by ext U; simp only [stock,stemPlug,if_neg h,ite_self]
variable {d₁ v₁ D₁ C₁ r₁:ℝ}
variable {V₁:Utopia H j v₁ d₁ r₁ C₁ χ} (hp₁:Solfege H V₁ uP)
include hp₁
lemma sap (q:Orders l) : Items H p (stock M H χ p uP q):=by
  by_cases h:Ψ; swap; · rw [stock_off M H χ p uP q h]; exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _=>rfl⟩
  unfold stock; by_cases he:q=perch l; simp_rw [if_neg (not_not.mpr he)]; exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _=>rfl⟩
  unfold stemPlug; simp_rw [if_pos he,if_pos h]; have hx (p':V l):= episodeSites (p:=Θ) H (show Kept H HG (flowerCup M H p uP p') from (honor M H p h.1.2).times (Copper.namesKept uP H hp₁ p' _ (Finset.biUnion_subset.mpr fun _ hi=> subset_biUnion_of_mem H.supportP (Finset.mem_sdiff.mp hi).1))) χ
  unfold convolve; exact ⟨fun U V'=> Finset.sum_congr rfl (fun i _=> (hx i).2.2 U V'),Finset.measurable_fun_sum _ (fun i _=> (hx i).1), fun U V' h=> Finset.sum_congr rfl (fun i _=> (hx i).2.1 _ _ h)⟩
variable {b A' R' Q' B' θ ζ c' ρ:ℝ} (N:Captain H j b' d v₀ w A b r B' R' (n+j) χ)
  (hB:LocalBookingsR2 ζ c' N.conduit)(h:1≤betaF G s L)(hζ:0≤ζ)(hH:1≤θ)(hp:1≤ρ)(hX:c'≤1)(hP:Charge.Allows l j θ)
local notation "Φ"=> N.conduit
omit hp₁
variable (hS:Copper.Solfege H N.conduit uP)
include hB h hζ hX hP U ht hH hS
lemma cameo_price (Y:Config G c) (hy:Healthy (Pressure.temp s) HG Y)(q:Orders l): Ore Y (stock M H χ p uP q) v₀ (receipt M H χ p N D x K θ q) j:=by
  have he: K≥0:= ht.salt; have hv:r≥1:= (Φ).active; have ht': D≥0:= U.fuel
  have hK : 0≤ speedS K r l:= by unfold speedS; positivity
  have hE :0≤ receipt M H χ p N D x K θ q:=recNN M H χ p ht U N hH q
  by_cases hΨ:(Ψ)∧ q≠ perch l; swap
  · intro E _ _ _ X x hs hy
    apply Brush.zi _ hE zero_le_one; exact Eventually.of_forall fun i=> (by unfold Function.comp stock; split; exact if_neg (fun h=>(hΨ ⟨h,by assumption⟩)); rfl)
  have hh(i:V l): Sees H j v₀ d χ (flowerCup M H p uP i) (M.weight*forge (Φ) θ i) (speedS K r l*(1+H.shapeW Θ)):=by
      refine Sees.climb H (Sees.times H (wave M H χ p ht hΨ.1.1) (Copper.tallFlock uP H hS i Finset.sdiff_subset hΨ.1.1.1.2 hP (slack _ hB h hζ hX))) le_rfl ?_; unfold speedS; nlinarith only [he]
  have hf (i:V l): Ore Y (episode H χ Θ (flowerCup M H p uP i)) v₀ (artA M H χ p N D x K θ i) j:= by
      exact episodeCost H N.oboe p.2.2 ((honor M H p hΨ.1.1.2).times (Copper.namesKept uP H hS i _ (Finset.biUnion_subset.mpr fun _ hi=> subset_biUnion_of_mem H.supportP (Finset.mem_sdiff.mp hi).1))) (Charge.holds U _ (mul_nonneg M.profit (forgeN _ hH i)) hK _ (hh i)) Y hy
  intro E _ _ _ U' x hw hU; unfold stock stemPlug receipt; simp_rw [if_pos hΨ.1,if_pos hΨ.2]; unfold convolve; exact Brush.spree _ (fun i v=> episode H χ Θ (flowerCup M H p uP i) (U' v)) _ zero_le_one fun i _=> hf i E U' x hw hU
end YM.LocalTaylorR2.Orbit
