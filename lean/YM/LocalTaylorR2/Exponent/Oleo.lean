import YM.LocalTaylorR2.Exponent.Rola

/-!
 # Capital. Keep actual regular support norm. Price in inverse β perturbative through total head, too. No fast growth assumption on calendar v. Fixed order p, spill tax to e.W.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Exponent
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves
variable {j k n l p m:ℕ} {g v d A D x y β:ℝ} {χ:Chi}
open PhysicalNext.Repeat Reel Strand Candle Tender Mesh LocalTaylorR2.Price Charge RG01.Survive
variable (Ξ:Observatory G){q:Orders k}{b t w A' r D' V' e ρ θ ζ c' u a:ℝ} (N:Captain H j b t v w A A' r D' e (n+j) χ) (hB:LocalBookingsR2 ζ c' N.conduit)(M:StoresR2 H j v t A D l x n χ) (F': Wealth Ξ H V' n x l m N.conduit k ρ)
local notation:max "Kx" => Candle.perch k
-- Define costs explicitly with apart on all *positions*, old on polluters.
def promotion (k:ℕ)(ρ:ℝ)(f:Orders k→ℝ)(q : Orders k) := f q + if q=Candle.perch k then ∑ i∈ Finset.univ.erase q, if i=0 then 0 else spelling k*(ρ^k)⁻¹ * f i else 0
def heavies (N:Captain H j b t v w A A' r D' e (n+j) χ) (D x θ ρ:ℝ) (U:H.ThinP) (q:Orders k):= promotion k ρ (schemePrice (l:=k) N D x θ U) q
def resultN (N:Captain H j b t v w A A' r D' e (n+j) χ)(θ ζ ρ D x :ℝ)(k:ℕ)(U:H.ThinP):= (1+spelling k)*result N θ ζ ρ D x k U
lemma capers (f:Orders k→ℝ)(h:∀ i,0≤f i)(hr:1≤ρ): (∑ q:Orders k, promotion k ρ f q *ρ^q.val) ≤ (1+spelling k)*(∑ q:Orders k,f q *ρ^q.val):=by
  let U:= Kx; let V:= Finset.univ.erase U; let t (i:Orders k) :=f i *ρ^i.val
  let A:=spelling k; have ht :0≤A:= spelling_pos k
  have hv q (hq:q∈V) : promotion k ρ f q=f q := by unfold promotion; rw [if_neg (show q≠Candle.perch k from ne_of_mem_erase hq),add_zero]
  let X(q:Orders k) := promotion k ρ f q *ρ^q.val
  let Z:=∑ i∈ V, if i=0 then 0 else A*(ρ^k)⁻¹ * f i
  have heq : (∑ q,X q)= (∑ q,t q)+ Z *ρ^(k+1):=by
     rw [← add_sum_erase _ _ (mem_univ U),←add_sum_erase _ t (mem_univ U),show (∑ i∈ Finset.univ.erase U,X i)=∑ i∈V,t i from Finset.sum_congr rfl (fun i hi=> by unfold X; rw [hv _ hi])]; unfold X promotion; rw [if_pos (show U=Kx from rfl),add_mul]; change t U+Z*ρ^(k+1)+(∑ i∈V,t i)=_; unfold V; ring
  change (∑ q,X q)≤ (1+A)*∑ q,t q; rw [heq, add_mul,one_mul]; apply add_le_add_right
  rw [←add_sum_erase _ t (mem_univ U),mul_add]; apply le_trans _ (le_add_of_nonneg_left (mul_nonneg ht (mul_nonneg (h _) (by positivity))))
  unfold Z; rw [Finset.sum_mul,Finset.mul_sum]; refine Finset.sum_le_sum ?_; intro i hi; split
  · rw [zero_mul]; exact mul_nonneg ht (mul_nonneg (h _) (by positivity))
  next he=> let e':= (i:ℕ); have hp:e'≠0:=fun hh=> he (Fin.ext hh); calc
        A*(ρ^k)⁻¹*f i* ρ^(k+1) = A*(f i*ρ):=by have hp:0<ρ:=zero_lt_one.trans_le hr; field_simp; ring
        _ ≤ _:= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_self_pow₀ hr hp) (h i)) ht
variable {δ:ℝ} (hp:Tail.GateR2 Q L μ s ρ θ D x D' r c' u δ ζ j k n)
include hp F' M hB
local notation:max "f'U"=> schemePrice (l:=k) N D x θ
lemma earns : ReadyAll χ (Mesh.issue H (Ξ.upgrade H k) χ (l:=k)) v j (heavies N D x θ ρ) (resultN N θ ζ ρ D x k) ρ:=by
  obtain ⟨hh,hρ,hθ,hζ,hT,hs,hl,hZ,hD,hU,hx,hV⟩:= hp
  have he:= LocalTaylorR2.Price.credentials N hB M hh hζ hρ hθ hs hl hZ hT
  let X:= Mesh.issue H (Ξ.upgrade H k) χ (l:=k); let f₀:=Candle.sprig H χ (l:=k)
  have hm:=LocalTaylorR2.Price.positional N M hθ (l:=k)
  let H' i q:= heavies N D x θ ρ i (k:=k) q
  have hh i {q}(h:q≠ Kx): H' i q= f'U i q:= by unfold H' heavies promotion; rw [if_neg h,add_zero]
  have hu:0≤ spelling k:= spelling_pos k
  constructor
  · intro i q; by_cases h:q=Kx
    · rw [h]; exact (highCatch H Ξ i N M F' hρ hθ).1
    exact (perchless H Ξ i N M F' hρ hθ q h).1
  · intro i q V hV; by_cases h:q=Kx; swap; · change Ore _ _ _ (H' i q) _; rw [hh i h]; exact ((perchless H Ξ i N M F' hρ hθ q h).2 V hV).1
    rw [h]; unfold heavies promotion; rw [if_pos (show Kx=Kx from rfl)]
    intro E _ _ _ V' x hv hM; apply ((he.budget i Kx V hV E V' x hv hM).gathering ((highCatch H Ξ i N M F' hρ hθ).2 V hV E V' x hv hM)).shimmy
    filter_upwards with y; change X i Kx _= (f₀ i Kx _)+ (X i Kx _ - f₀ i Kx _); ring
  · exact hρ
  · intro i q; by_cases h:q= Kx; swap; · change 0≤ H' i q; rw [hh i h]; exact he.pos _ _
    rw [h]; unfold heavies promotion; rw [if_pos (show Kx=Kx from rfl)]; apply add_nonneg (hm ..) (sum_nonneg ?_); intro q _; split <;> first | exact le_rfl | exact mul_nonneg (by positivity) (hm ..)
  · exact fun i=> (capers (f'U i) (hm i) hρ).trans (mul_le_mul_of_nonneg_left (he.bounds i) (add_nonneg zero_le_one hu))
  exact fun i V=> floorplan H _ χ i V k
omit F'
open AnalyticBridge VerifiedReset
lemma medals (hc:a+δ+δ ≤ Q.exp)(hd:0<δ)(hv:(1+spelling k)*secondQ Q L μ s θ ρ D x D' r c' k n j ≤ u) : Ready H.smallAt (radiusB s) (fun i=>2^j* (resultN N θ ζ ρ D x k i)) (a+δ) u δ (1/2):=by
  obtain ⟨hh,hρ,hθ,hζ,hT,hs,hl,hZ,hD,hU,hx,hV⟩:= hp; have hz : 0≤ 1+spelling k:=by linarith [spelling_pos k]
  have ht:= Quotes.hit_scale hz (LocalTaylorR2.Price.funds N hB M hh hζ hρ hθ hD hc)
  refine ⟨hV,hd,hx,(by norm_num),fun i=>mul_nonneg (by positivity) (mul_nonneg hz (LocalTaylorR2.Price.tall N M hh hζ hρ hθ _)),fun i=>?_⟩
  apply budget_loosen _ hv; unfold resultN; simp_rw [show ∀ X:ℝ,2^j*((1+spelling k)*X)=(1+spelling k)*(2^j*X) from fun X=> by ring]; exact ht i
end YM.LocalTaylorR2.Exponent
