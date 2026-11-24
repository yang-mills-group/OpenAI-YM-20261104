import YM.LocalTaylorR2.Orbit.Lantern
/-! Budget packets for a real Crew on track alphabet. -/
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
abbrev assembly (q:V l): Port.Test T:= fun _ X u=> M.paidU X o.a (worldZ X R.beta u)* letters H q _ X u
abbrev papery(q:V l):= episode H χ Θ (assembly M H p q)
lemma service (h:Orbit.checked M H p)(q:V l):Kept H HG (assembly M H p q) := (honor M H p h.2).times (letterSect H q HG (biUnion_subset.mpr (fun _ hi=> subset_biUnion_of_mem H.supportP ((mem_sdiff.mp hi).1))))
lemma roll_forward (hq:(Ψ)) (l:ℕ) (w:Air f G): Orbit.hero M H p F X w= ∑ q:V l, assembly M H p q F X w := by unfold Orbit.hero assembly; rw [← test_eq H _ (isPure hq.2), running H l, Finset.mul_sum]
def press (q:Orders l) (U:Config G c):= if Ψ then convolve (U:=T₀) q (fun i=> papery M H χ p i U) else 0
def graded (q:Orders l) (U:Config G c):=if q=perch l then deck M H χ p U-∑ r∈univ.erase q,press M H χ p r U else press M H χ p q U
lemma beams_split (U:Config G c):deck M H χ p U=∑ q:Orders l, graded M H χ p q U:=by
  let z:= perch l; rw [← add_sum_erase _ _ (mem_univ z),graded, if_pos (rfl:z=perch l), sub_add_eq_add_sub]
  have hx : ∑ i∈univ.erase z,graded M H χ p i U=∑ i∈univ.erase z,press M H χ p i U := sum_congr rfl fun i hi=> if_neg (ne_of_mem_erase hi)
  rw [hx]; ring
lemma graded_off (h:¬Orbit.checked M H p) (q:Orders l):graded M H χ p q=fun _=>0:= by ext; simp [deck,h,graded,press]
lemma graded_dead (h:¬ (Ψ))(q:Orders l): graded M H χ p q= if q=perch l then deck M H χ p else 0:=by funext i; simp only [graded,press,ite_apply]; simp only [if_neg h,sum_const_zero,sub_zero,Pi.zero_apply]
lemma holding (q:Orders l): Items H p (graded M H χ p q):=by
  by_cases h:Orbit.checked M H p; swap; · rw [graded_off M H χ p h]; exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _=>rfl⟩
  have hF:= episodeSites H (hero_test M H p h.2) χ
  have ht(q:Orders l): Items H p (press M H χ p q):=by
    unfold press; by_cases he:Ψ; swap; · simp_rw [if_neg he]; exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _=>rfl⟩
    simp_rw [if_pos he]; have hx (p':V l):= episodeSites (p:=Θ) H (service M H p h p') χ
    exact ⟨fun U V'=> Finset.sum_congr rfl (fun i _=> (hx i).2.2 U V'),Finset.measurable_fun_sum _ (fun i _=> (hx i).1), fun U V' h=> Finset.sum_congr rfl (fun i _=> (hx i).2.1 _ _ h)⟩
  unfold graded; by_cases he:q=perch l; swap; · simp_rw [if_neg he]; exact ht _
  simp_rw [if_pos he,deck,if_pos h]
  exact ⟨fun U V'=> congr_arg₂ (·-·) (hF.2.2 U V') (Finset.sum_congr rfl fun i _=> (ht i).1 U V'), hF.1.sub (Finset.measurable_fun_sum _ fun i _=> (ht i).2.1),fun U V' h=> congr_arg₂ (·-·) (hF.2.1 _ _ h) (sum_congr rfl fun i _=> (ht i).2.2 U V' h)⟩
variable {b A' R' Q' B' θ ζ c' ρ:ℝ} (N:Captain H j b' d v₀ w A b r B' R' (n+j) χ)
  (hB:LocalBookingsR2 ζ c' N.conduit)(h:1≤betaF G s L)(hζ:0≤ζ)(hH:1≤θ)(hp:1≤ρ)(hX:c'≤1)(hP:Charge.Allows l j θ)
local notation "Φ"=> N.conduit
include N in
lemma ghost (h:(Ψ)) (q:Orders l)(Z:Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (F:Z→ Config G c) (x:Z) (he:Mode F x j v₀)(hv:Healthy (Pressure.temp s) HG (F x)): graded M H χ p q ∘ F =ᶠ[𝓝 x] press M H χ p q ∘ F:=by
  by_cases hq:q=perch l; swap; · exact Eventually.of_forall fun _=> if_neg hq
  have hh:= episodeSum (H0:=fun F X w=>roll_forward M X H p h _ w) N.oboe p.2.2 he (H:=H) (hero_test M H p h.1.2) (g:=assembly M H p (l:=l)) (fun i=>service M H p h.1 i) hv
  filter_upwards [hh] with y hy; dsimp only [Function.comp_apply,graded]; rw [if_pos hq]; apply sub_eq_iff_eq_add.mpr
  rw [show press M H χ p q (F y)+ (∑ t∈ univ.erase q,press M H χ p t (F y))= _ from add_sum_erase _ (fun t=> press M H χ p t (F y)) (mem_univ q),deck,if_pos h.1];
  simp_rw [press,if_pos h]; rw [Candle.collects]; exact hy
-- one wagon with crude polyPrice. Formation against all Θ even non-Clear. Θ cardinal burnt not Taylor. radius ρ for funding per birth.
abbrev truck (D x' K r:ℝ)(l j:ℕ):= x'*(1+D+speedS K r l)^j
-- speedS definition ok? arguments e..
local notation "γ"=> (1+H.shapeW Θ)^(n+j)
abbrev artA (D x' K θ:ℝ)(q:V l):= M.weight*forge (Φ) θ q*truck D x' K r l j*γ
def receipt (D x K θ:ℝ) (q:Orders l):= if Ψ then convolve (U:=T₀) q (fun i=> artA M H χ p N D x K θ i) else if q=perch l∧Orbit.checked M H p then M.weight* (∏ i∈T₀, (Φ).fare i)*truck D x K r l j*γ else 0
-- passport: Ore every field in full U
include ht U hH
lemma artNN (q:V l):0≤ artA M H χ p N D x K θ q:=by
  have hh:= (Φ).active; have h:= forgeN (Φ) hH q; have hX:= U.sure; have hf:= U.fuel; have hp:= H.positive_volume Θ;have hT:=ht.salt;have hm:= M.profit; unfold artA truck speedS; positivity
lemma recNN(q:Orders l):0≤ receipt M H χ p N D x K θ q:=by
  unfold receipt; split
  · exact Finset.sum_nonneg fun _ _=> artNN M H χ p ht U N hH _
  split
  · have he:0≤ (∏ i∈ T₀, (Φ).fare i):= prod_nonneg fun _ _=> (Φ).fares _; unfold truck speedS; have hh:= (Φ).active; have hX:= U.sure; have hf:= U.fuel; have hp:= H.positive_volume Θ; have hT:=ht.salt; have hm:= M.profit; positivity
  exact le_rfl
include hB h hζ hX hP
lemma recovers (Y:Config G c) (hy:Healthy (Pressure.temp s) HG Y)(q:Orders l): Ore Y (graded M H χ p q) v₀ (receipt M H χ p N D x K θ q) j:=by
  have he: K≥0:= ht.salt; have hv:r≥1:= (Φ).active; have ht': D≥0:= U.fuel
  have hK : 0≤ speedS K r l:= by unfold speedS; positivity
  by_cases hΨ:(Ψ)
  · have hh(i:V l): Sees H j v₀ d χ (assembly M H p i) (M.weight*forge (Φ) θ i) (speedS K r l*(1+H.shapeW Θ)):=by
      refine Sees.climb H (Sees.times H (wave M H χ p ht hΨ.1) (sumSpeed hB i (show T₀⊆ Θ from Finset.sdiff_subset) hΨ.1.1.2 hP (slack _ hB h hζ hX))) le_rfl ?_; unfold speedS; nlinarith only [he]
    have hf (i:V l): Ore Y (papery M H χ p i) v₀ (artA M H χ p N D x K θ i) j:=by
      exact episodeCost H N.oboe p.2.2 (service M H p hΨ.1 i) (Charge.holds U _ (mul_nonneg M.profit (forgeN _ hH i)) hK _ (hh i)) Y hy
    intro E _ _ _ U' x hw hU; apply Brush.shimmy _ (ghost M H χ p N hΨ q E U' x hU (hw.symm ▸ hy)); unfold press receipt; simp_rw [if_pos hΨ]; unfold convolve; exact Brush.spree _ (fun i v=> papery M H χ p i (U' v)) _ zero_le_one fun i _=> hf i E U' x hw hU
  rw [graded_dead M H χ p hΨ q,receipt,if_neg hΨ]; by_cases hF: q=perch l ∧ Orbit.checked M H p; swap
  · rw [if_neg hF]; have hez (i:Config G c): (if q=perch l then deck M H χ p else 0) i=0:=by by_cases hv' : q=perch l; · rw [if_pos hv']; exact if_neg (fun h=> hF ⟨hv',h⟩)
                                                                                             rw [if_neg hv']; rfl
    intro E _ _ _ U x ht hx; apply Brush.zi (Eventually.of_forall fun t=> hez _) le_rfl zero_le_one
  have hs := episodeCost H N.oboe p.2.2 (hero_test M H p hF.2.2) (flour M H χ p (Φ) ht U hF.2) Y hy
  rw [if_pos hF,if_pos hF.1, show deck M H χ p= _ from funext fun _=> if_pos hF.2] -- goal equality heuristic
  intro E _ _ _ U' x' ht'' hV; apply (hs E U' x' ht'' hV).climb _ le_rfl
  let a:= M.weight*(∏ i∈ T₀, (Φ).fare i)*(1+ H.shapeW Θ)^(n+j)
  have hA: 0 ≤ a:= mul_nonneg (mul_nonneg M.profit (prod_nonneg (fun _ _=> (Φ).fares _))) (pow_nonneg (add_nonneg zero_le_one (H.positive_volume _)) _)
  have hy : 2*(r+K)≤ speedS K r l:= by unfold speedS; nlinarith [Nat.cast_nonneg (α:=ℝ) l]
  calc _ = x*(1+D+2*(r+K))^j*a:=by unfold a; ring
       _ ≤ truck D x K r l j *a:= by unfold truck; have hX:=U.sure; gcongr
       _ = _:=by unfold a; ring
end YM.LocalTaylorR2.Orbit
