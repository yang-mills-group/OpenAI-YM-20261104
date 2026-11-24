import YM.X.Tot.Spark
/-! # SymmetricCost occupancy ∼. report constraints fixed. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed Shelf
open Stems hiding X
open Ocean Haze Fielding Print Fund Tri Plate LiftMark Hinge Bare Pulse Labels Pert.RawLabels Crystal Gravity
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {F: Labels.Frames G} {d k:ℕ} {V I:Type*} {r R:ℝ} {n:Side}
local notation "F₀"=> (fades ℂ)
local notation "L"=>(atTop:Filter ℕ)
abbrev CostF (f g:ℕ→ℂ):Prop:= f-g∈ F₀
section cost
variable {a b c d f g:ℕ→ℂ}{x:ℂ}
lemma HasF (h:CostF f g):Tendsto (f-g) L (𝓝 0):=h
namespace CostF
lemma goes (h:CostF f g) : Tendsto f L (𝓝 x) ↔ Tendsto g L (𝓝 x):= by
    constructor; · intro H; have ht:= H.sub (HasF h); rw [sub_zero] at ht; exact ht.congr (fun i=> sub_sub_self ..)
    intro H; have ht:= (HasF h).add H; rw [zero_add] at ht; exact ht.congr (fun i=> sub_add_cancel ..)
lemma reflexive : CostF f f:= by rw [CostF,sub_self];exact (F₀).zero_mem
lemma sym (h:CostF f g): CostF g f:= by unfold CostF; rw [← neg_sub];exact (F₀).neg_mem h
lemma trans (h:CostF a b)(hh:CostF b c) : CostF a c:= by rw [CostF,show a-c=(a-b)+(b-c) by ring]; exact (F₀).add_mem h hh
lemma add (h:CostF a b)(hh:CostF c d): CostF (a+c) (b+d):= by rw [CostF,add_sub_add_comm];exact (F₀).add_mem h hh
lemma sub (h:CostF a b)(hh:CostF c d): CostF (a-c) (b-d):= by rw [CostF,sub_sub_sub_comm];exact (F₀).sub_mem h hh
lemma neg (h:CostF f g):CostF (-f) (-g):= by simpa using sub (a:=0) reflexive h
lemma mul (h:CostF f g)(ht:Released a):CostF (a*f) (a*g):= by rw [CostF,← mul_sub];exact usual_fading a _ ht h
lemma scalar (h:CostF f g)(t:ℂ): CostF (t • f) (t • g):= mul h (constell t)
lemma fin (f g:I→ℕ→ℂ)(s:Finset I)(h:∀ i∈s,CostF (f i) (g i)) : CostF (∑ i∈s,f i) (∑ i∈s,g i):= by rw [CostF,←Finset.sum_sub_distrib];exact (F₀).sum_mem h
lemma zero (h:f∈fades ℂ):CostF f 0:= by simpa [CostF] using h
lemma sterile (h:CostF f 0): Tendsto f L (𝓝 0):= (h.goes).mpr tendsto_const_nhds
end CostF
end cost
variable (q:ℕ+)(χ:Floor R)
local notation "Q"=> qu q G
local notation "Ω"=> Foam G
variable (x y z:Fielding.Walk) {p p' a a' b b': Foam G}
local notation "Θ"=> (Reed.Horizontal G)
local notation "Gτ" => gather q x y z
local notation "Tχ"=> priceF q χ x y z
variable (h:Geom q r x y z)(hr:0<r)(hq:1<q.val)
include h hr hq
lemma replace_fields (hx:Apt q r p)(ha:a-a'∈ Ash q Θ)(hb:b-b'∈ Ash q Θ)(hv:a'∈ Ready q Θ)(hw:b∈Ready q Θ): CostF (Gτ p a b) (Gτ p a' b'):= by
    have he: CostF (Gτ p a b) (Gτ p a' b):= by rw [CostF,gather_s q x, gather_s q x,← gather_sub, gather_s q y]; exact ash_second q x y z p _ b h hr hq hx ha hw
    refine he.trans ?_; rw [CostF,gather_swap q x y z p, gather_swap q x y z p, gather_s q x, gather_s q x, ← gather_sub, gather_s q z]; exact ash_second q x z y p (b-b') a' (h.swap q ..) hr hq hx hb hv
omit hr
include χ
lemma price_sub (h':R<r) (a a' b p:Foam G)(H:a-a'∈Ash q Θ)(he:b∈Ready q Θ)(hp:p∈ Ready q Θ): CostF (Tχ a b p (EngineP q G)) (Tχ a' b p (EngineP q G)):= by
   let t:=EngineP q G; have hx:=price_add q χ x y z (a-a') a' b p t; rw [sub_add_cancel a a'] at hx; rw [CostF,hx,add_sub_cancel_right]; exact ash_full q χ x y z (a-a') b p h hq h' H he hp
lemma replace_bill(h':R<r)(ha:a-a'∈ Ash q Θ)(hb:b-b'∈ Ash q Θ)(hp:p-p'∈ Ash q Θ)(hc:a∈ Ready q Θ)(hd:b∈Ready q Θ)(he:p'∈Ready q Θ)(hf:a'∈Ready q Θ): let v:= EngineP q G; CostF (Tχ p a b v) (Tχ p' a' b' v):= by
    intro v; refine (price_sub q χ x y z h hq h' p p' a b hp hc hd).trans ?_; rw [price_c q χ x y z,price_c q χ x y z]; let w:= h.circles q x y z; refine (price_sub q χ y z x w hq h' a a' b p' ha hd he).trans ?_; rw [price_c q χ y z x,price_c q χ y z x]; exact price_sub q χ z x y (w.circles q ..) hq h' b b' p' a' hb he hf
end YM.PositionX.Tot
