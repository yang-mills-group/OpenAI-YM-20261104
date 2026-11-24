import YM.LocalTaylorR2.Exponent.Rack
import YM.LocalTaylorR2.Copper.Bloom
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
open Marker Charge Tender Exponent
lemma namesCol {p':Molecule S}{Ξ:Copper.Stems T}(q:Paint p' m)(hq:Candle.chooseSlot q≠ Candle.perch m) : Copper.namesP Ξ q=Exponent.rafters Ξ q:= funext fun _=>funext fun _=> funext fun _=> Finset.prod_congr rfl fun _ _=> noOvercharge hq .. -- linter dummy
variable {j l k n:ℕ} {D K e v₀ d r z x b' A ζ θ :ℝ}
local notation "HG"=> H.unionP Θ
local notation "T₀"=> restP M H p
local notation "Ψ"=> Orbit.checked M H p ∧ Clear T₀
lemma gripP {Ξ:Bevy T}(q:Paint (T₀) l)(hq:chooseSlot q ≠ Candle.perch l)(h:∀ i,Port.Burst H (H.supportP (identityLog i)) (Ξ i))(hc:Orbit.checked M H p) : Port.Burst H HG (flowerCup M H p Ξ q):=by
  unfold flowerCup; rw [namesCol q hq]; refine (Port.Burst.fat (honor M H p hc.2)).times (Exponent.glow H _ q _ (Finset.biUnion_subset.mpr fun _ hi=> subset_biUnion_of_mem H.supportP (Finset.mem_sdiff.mp hi).1) (fun i _=> h _))
lemma sapP (q:Orders l)(ψ:Copper.Stems T)(hp:∀ i,Port.Burst H (H.supportP (identityLog i)) (ψ i)): Items H p (stock M H χ p ψ q):=by
  by_cases h:Ψ; swap; · rw [stock_off M H χ p ψ q h]; exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _=>rfl⟩
  unfold stock; by_cases he:q=Candle.perch l; simp_rw [if_neg (not_not.mpr he)]; exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _=>rfl⟩
  unfold stemPlug; simp_rw [if_pos he,if_pos h]; let P' := univ.filter fun j:Paint T₀ l=> chooseSlot j=q; have hx i (hi:i∈P'):= episodeSitesBurst H (p:=Θ) (gripP M H p i (ne_of_eq_of_ne (mem_filter.mp hi|>.2) he) hp h.1) χ
  unfold convolve; exact ⟨fun U V'=> Finset.sum_congr rfl (fun i hi=> (hx i hi).2.2 U V'),Finset.measurable_fun_sum _ (fun i hi=> (hx i hi).1), fun U V' h=> Finset.sum_congr rfl (fun i hi=> (hx i hi).2.1 _ _ h)⟩

variable {ψ:Copper.Stems T}{b B B' R':ℝ}(N:Captain H j b' d v₀ w A b r B' R' (n+j) χ)(ht: Tinted G s K d o.a L χ j)(U:StoresR2 H j v₀ d A D k x n χ)
variable (hS:Exponent.Lodestar H m B N.conduit ψ) (hM:Exponent.Bank H j k n x l m B)
include U ht hS hM
lemma arriveB (Y:Config G c)(hH:1≤θ)(hX:1≤B)(hy:Healthy (Pressure.temp s) HG Y)(q:Orders l): Ore Y (stock M H χ p ψ q) v₀ (receipt M H χ p N D x K θ q) j:=by
  let Φ:=N.conduit; have he: K≥0:= ht.salt; have hv:r≥1:= Φ.active; have ht': D≥0:= U.fuel
  have hK : 0≤ speedS K r l:= by unfold speedS; positivity
  have hE :0≤ receipt M H χ p N D x K θ q:=recNN M H χ p ht U N hH q
  by_cases hΨ:(Ψ)∧ q≠ Candle.perch l; swap
  · intro E _ _ _ X x hs hy; apply Brush.zi _ hE zero_le_one; exact Eventually.of_forall fun i=> (by unfold Function.comp stock; split; exact if_neg (fun h=>(hΨ ⟨h,by assumption⟩)); rfl)
  let x' := univ.filter fun p:Paint T₀ l=> chooseSlot p=q
  have hh(i:Paint (T₀) l)(hi:i∈x'): let x:= speedS K r l*(1+H.shapeW Θ)
      Exponent.Rates H HG j m l B v₀ d χ (flowerCup M H p ψ i) (M.weight*forge Φ θ i) x:=by
      have hx:=mem_filter.mp hi|>.2; have hvX:= ne_of_eq_of_ne hx hΨ.2; intro x; unfold flowerCup; rw [namesCol i hvX]
      have hw : inserts i≤l:= by
          by_contra hk; push Not at hk; exact hvX (Fin.ext (show min _ _=_ from min_eq_left hk))
      intro E _ _ _ X V U' y w x₀ z e he hF hg ht' hI; have he:= Exponent.Rates.times H (Exponent.Rates.era H HG B m (wave M H χ p (v₀:=v₀) ht hΨ.1.1)) (Exponent.tall (Ξ:=ψ) (H:=H) hS hX i (Θ) Finset.sdiff_subset hΨ.1.1.1.2 hw hH) E X V U' y w x₀ z e he hF hg ht' hI
      rw [Nat.zero_add] at he; apply he.climb le_rfl ?_; unfold x speedS; nlinarith only [‹0≤K›] -- maybe local notation x captured
  have hf i (hi:i∈x'): Ore Y (episode H χ Θ (flowerCup M H p ψ i)) v₀ (artA M H χ p N D x K θ i) j:= by
      exact episodeCostBurst H N.oboe p.2.2 (gripP M H p i (ne_of_eq_of_ne (mem_filter.mp hi|>.2) hΨ.2) hS.love hΨ.1.1) (Exponent.Rates.elans H hM U (hh i hi) hX (mul_nonneg M.profit (forgeN _ hH i)) hK) Y hy
  intro E _ _ _ U' x hw hU; unfold stock stemPlug receipt; simp_rw [if_pos hΨ.1,if_pos hΨ.2]; unfold convolve; exact Brush.spree _ (fun i v=> episode H χ Θ (flowerCup M H p ψ i) (U' v)) _ zero_le_one fun i hi=> hf i hi E U' x hw hU
end YM.LocalTaylorR2.Orbit
