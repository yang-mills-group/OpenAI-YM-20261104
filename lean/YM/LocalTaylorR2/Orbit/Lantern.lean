import YM.LocalTaylorR2.Orbit.Hero
import YM.LocalTaylorR2.Marker.Light
/-! Quantitative Multi (arbitrary Mark crew) before project, at all Soft apertures. -/
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
private lemma span_pos (i:Head S) : 0≤ spanW T R (radiusB s) Q.halo i:=by
   rcases i with i|i; exact zero_le_one; exact add_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
include hc ht
lemma wave : Sees H j v₀ d χ (fun _ X u=> M.paidU X o.a (worldZ X R.beta u)) M.weight (2*K*H.shapeW Θ):=by
   have hm(k:Leaf R):= Marker.markedSees k H ht (v₀:=v₀)
   have hA:= Sees.collect H M.own (fun i hi=> hm i)
   apply Sees.climb H hA le_rfl
   let f i:=spanW T R (radiusB s) Q.halo i
   have he: Set.InjOn (fun i:Leaf R=> i.turn.badge S) M.own:= fun i hi j hj h=> M.alone hi hj (Team.badged S h)
   have hv: ∑ i∈ M.own,f (i.turn.badge S)=∑ i∈ Ω, f i:=by simp only [Team.signs, Finset.sum_image he] -- packing
   rw [← Finset.mul_sum,hv]; exact (mul_le_mul_of_nonneg_left ((Finset.sum_le_sum_of_subset_of_nonneg hc.2 (fun i _ _=>span_pos i)).trans (Utopia.worthy _ hc.1.2)) ht.salt).trans_eq (by ring)
set_option quotPrecheck false
local notation "wH"=> (Ξ.rad^ (blaze Θ).card)
local notation "ĝ"=> (H.shapeW Θ)
omit hc ht in
lemma blossom_id : blaze T₀=blaze Θ:= by
  ext i; let X' : Head S:= Sum.inr (.inr (.inr i))
  change i∈ _ ↔ i∈_; simp only [blaze,restP,mem_toRight]; constructor; · exact fun h=>(Finset.mem_sdiff.mp h).1
  intro hi; refine Finset.mem_sdiff.mpr ⟨hi,fun hv=>?_⟩
  obtain ⟨j,hj,hj'⟩:=mem_image.mp hv;change j.turn.badge S=X' at hj'; rcases h:j.turn with i|i <;> simp [h,X',Wing.badge] at hj'
local notation "hθ"=> (2*(r+K)*(1+ĝ))
lemma hectare (Y:Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (V:Y → Config G c) (u:Y→Directions G f) (z:Y→ Air f G) (a:Y) (w:Air f G)
      (hx:X.x=s)(hχ:X.χ=χ)(hv:X.manifest)(hl:X.width=o.K)(hp:Healthy (Pressure.temp s) HG X.V)(hV: Mode V a j v₀)(hh : Clutch X w o.a R.beta d a j V u z) :
    Brush j ((X.catastrophe (o.ξ/2) R.beta (blaze Θ)).indicator (fun _=> M.weight*∏ i∈ T₀, Ξ.tag i) w) hθ (fun y=> hero M H p F (vary X (V y)) (z y)) a:= by
  let S' := X.catastrophe (o.ξ/2) R.beta (blaze Θ)
  let f (i:Head S) y := Polar.ember (vary X (V y)) o.a R W Q.table (u y) (X.input (worldZ X R.beta w)) (z y) (own Θ) Q.halo i
  let g y:= M.paidU (vary X (V y)) o.a (worldZ (vary X (V y)) R.beta (z y)); let h y:= g y*∏ i∈T₀, f i y
  have hh' : (fun y=> hero M H p F (vary X (V y)) (z y))=ᶠ[𝓝 a] h:= by
    filter_upwards [hh.patch] with y hy
    apply congr_arg (g y*·)
    unfold Polar.floating; rw [hh.moving y]
    exact Finset.prod_congr rfl fun i _=> (plastic hy hh.pulse).reeled (show Room P S _ (vary X (V y)).x from hx.symm ▸ H.laws.data.room) W Q.table (own Θ) Q.halo (show Intake P _ (vary X (V y)).x R from hx.symm ▸ H.laws.intake) i (z y)
  apply Brush.shimmy _ hh'
  have hΞ':= Ξ.stream Y F X V u z a w hx hl hχ hv hV hh; have hr:0≤r:= zero_le_one.trans Ξ.active; have h' : 0≤K:= ht.salt
  have hθP : 0 ≤ hθ:= mul_nonneg (mul_nonneg zero_le_two (add_nonneg hr h')) (add_nonneg zero_le_one (H.positive_volume _))
  by_cases hy:w∈S'
  · rw [Set.indicator_of_mem hy]
    have he i (hi : i∈T₀) : Brush j (Ξ.tag i) (r*spanW T R X.B Q.halo i) (f i) a := by
      have he:= hΞ' (own Θ) i (Finset.disjoint_of_subset_left (subset_biUnion_of_mem H.supportP ((mem_sdiff.mp hi).1)) (show Healthy (temp X.x) _ _ from hx.symm ▸ hp))
      unfold Utopia.tag; rw [← show X.B=radiusB s from congr_arg radiusB hx]; exact he
    apply (((wave M H χ p ht hc) Y F X V u z a w hx hl hv hχ hV hh).paints (Brush.all_prod T₀ f _ _ he)).climb le_rfl
    rw [← Finset.mul_sum,show X.B=radiusB s from congr_arg radiusB hx]
    apply le_trans (add_le_add_right (mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg (show T₀⊆Θ from Finset.sdiff_subset) (fun j _ _ => span_pos j)).trans (Utopia.worthy _ hc.1.2)) hr) _)
    nlinarith only [h',hr]
  rw [Set.indicator_of_notMem hy]; refine Brush.zi ?_ le_rfl hθP
  unfold S' at hy; rw [← blossom_id M H p] at hy
  unfold catastrophe Poll.Crash at hy; change ¬(∀ i∈_,∃ j, _≤_ ∧ _≤_) at hy; push Not at hy
  obtain ⟨i,hi,hp'⟩:= hy
  have hc : Cash W X.x μ L Q o C T R := hx.symm ▸ H
  have hx := hh.sleek hc hV Ξ.clock hv hl i (fun i hi=> (hp' i hi).le) (own Θ)
  filter_upwards [hx] with t hZ
  exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (mem_toRight.mp (mem_toRight.mp (mem_toRight.mp hi))) hZ)

include U
local notation "θ"=> (2*(r+K))
-- include reserve under Fleet
lemma flour : IntegrandCost H HG (hero M H p) j A v₀ (M.weight*x*((1+D+(2*(r+K)))^j)*(1+ĝ)^(n+j) *∏ i∈ T₀, Ξ.fare i) χ:= by
  refine ⟨?_⟩; intro F X hx hk hm hX hU E _ _ _ V y hV hy m I
  let Z:=1+ĝ; let B:=M.weight* ∏ i∈T₀, Ξ.tag i; let a:= B*(1+D+θ)^j*Z^j
  have hS:1≤Z:=le_add_of_nonneg_right (H.positive_volume _); have hD:0≤ D:= U.fuel; have h:0≤θ:= mul_nonneg zero_le_two (add_nonneg (zero_le_one.trans Ξ.active) ht.salt)
  have hB:0≤B:= mul_nonneg M.profit (prod_nonneg fun i _=>Ξ.tagged _)
  have ha:0≤ a:= by unfold a; positivity
  let J:= X.catastrophe (o.ξ/2) R.beta (blaze Θ); let f(z:Air f G):= facescale I z^(k*j)
  obtain ⟨hF,hF'⟩:= U.curtain Θ F X hx hX hk hm a ha (wH) (pow_nonneg Ξ.awake _) J (Poll.sounded ..) (by rw [← pow_mul,Nat.mul_comm,pow_mul]; exact Ξ.ship _ X hx hk hX hm (blaze Θ))
  refine ⟨fun z=> a*J.indicator f z.2,hF,hF'.trans_eq ?_,?_⟩
  · unfold a B Z; rw [Ξ.remixes,blossom_id]; ring
  intro ⟨w,z⟩; let Y:= X.wrapY w; obtain ⟨hw,hq⟩:= U.flight F Y hx hX hk hm z E V y hy hV; have hh : Healthy (temp s) HG X.V:= hU
  have he:=((hq Θ|>.paints (hectare M (X.wrapY w) H χ p Ξ ht hc E V _ _ _ z hx hX hm hk hh hV hw)).trim); apply he.climb _ le_rfl
  change 1*J.indicator (fun _=> B) z*(1+(D*facescale I z^k+θ*Z))^j ≤ a*J.indicator f z
  by_cases hl:z∈ J; swap; · rw [Set.indicator_of_notMem hl,Set.indicator_of_notMem hl,mul_zero, zero_mul,mul_zero]
  rw [Set.indicator_of_mem hl,Set.indicator_of_mem hl,one_mul]; let K':=facescale I z
  have he:1≤K':= (Flux.expenses I z).1
  have H0 : 0 ≤ D*K'^k:=by positivity
  have hy':(1+(D*K'^k+(θ)*Z))≤(1+D+θ)*Z*K'^k:=by
    have hv:= one_le_mul_of_one_le_of_one_le hS (one_le_pow₀ (n:=k) he)
    have hB:K'^k≤ Z*K'^k:= le_mul_of_one_le_left (by positivity) hS
    have hL:Z ≤ Z*K'^k:= le_mul_of_one_le_right (zero_le_one.trans hS) (one_le_pow₀ he)
    nlinarith only [hv,mul_le_mul_of_nonneg_left hB hD,mul_le_mul_of_nonneg_left hL h]
  exact le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0≤1+(D*K'^k+(θ)*Z) by positivity) hy' j) hB) (le_of_eq (by unfold a f; unfold K'; rw [pow_mul,mul_pow, mul_pow]; ring))
end YM.LocalTaylorR2.Orbit
