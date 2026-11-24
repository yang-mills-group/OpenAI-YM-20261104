import YM.LocalTaylorR2.Marker.Light
import YM.LocalTaylorR2.License
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
local notation "cR" => Q.costs L μ R.beta x C'
-- aggressive upper price per marked occurrence. Other partners unchanged.
def hook (y η ζ:ℝ)(i:Head S):ℝ:= if i=i₀ then y*jewel M Q L x else entry Ξ η ζ i

include H M Ξ
section ticket
variable (h : 1≤betaF G x L) (hζ:0≤ζ) (hp:1≤η) (hy:1≤y) (hI:LocalBookingsR2 ζ c' Ξ)
  (hA:foam Q L) (hK:R.p.B≤2*radiusB x)
local notation "Ix" => Mixed.lengths S (cR) (ConnectedActivityE6.lengths T R)
local notation "Sx" => (current Q L μ x + (η*c'+y*ribbon Q L x))
variable (hv: degreePrice (radiusB x) (current Q L μ x + (η*c'+y*ribbon Q L x)) Q.δ ≤ 1/2)
include h hζ hp hy
lemma hookN (i:Head S): 0 ≤ hook M H Ξ y η ζ i:=by
  unfold hook
  split; exact mul_nonneg (zero_le_one.trans hy) (dew M H).1.le; exact (Ξ.fares _).trans (cheap _ h hζ hp _)
include hI hA hK hv
omit hζ in
lemma turnstile : Ready H.supportP (radiusB x) (Reserves.tariff (hook M H Ξ y η ζ) Ix 0 Q.ε)
    (Q.exp+2*Q.ε) Sx Q.δ (1/2) := by
  let r(q':Alphabet c f):= if q'=Daisy.sparkling c f M.turn then y*jewel M Q L x else raiseT Ξ η ζ q'
  let K:= η*c'+y*ribbon Q L x; let R':=higher (cR) K
  let g:=raiseT Ξ η ζ; let u(q':Alphabet c f):= y*colly (fun _ => 0) M Q L x q'
  have ht:0 ≤ y*ribbon Q L x:=mul_nonneg (zero_le_one.trans hy) (mul_nonneg (Daisy.arable H).le (Real.exp_pos _).le)
  have hC : 0≤K:= add_nonneg (mul_nonneg (zero_le_one.trans hp) (budget_nonneg (hI.leases.hit 0))) ht
  have hz:= Raw.boost_price hI.leases (zero_le_one.trans hp)
  have hz' : Ac.Hit H.birth (radiusB x) (tariff u (ConnectedActivityE6.lengths T R) (fun _=>0) Q.ε) Q.relative (y*ribbon Q L x):= by
    have he := AnalyticBridge.VerifiedReset.Quotes.hit_scale (zero_le_one.trans hy) (sustains M H hA hK)
    convert he using 1; ext i; dsimp only [tariff,u]; ring
  have hu i: 0≤ u i:= by
    unfold u colly; split
    next => exact mul_nonneg (zero_le_one.trans hy) (dew M H).1.le
    next => rw [mul_zero]
  have hr i: 0≤ r i:=by
    unfold r;split
    next => exact mul_nonneg (zero_le_one.trans hy) (dew M H).1.le
    next => exact hz.nonneg i
  have hh : Accounts S Q.halo (radiusB x) R' H.birth r (ConnectedActivityE6.lengths T R) (steamP S (cR)):= by
    refine ⟨Ξ.accrues.packetBound,hr,Ξ.accrues.extra,fun i=> budget_loosen (C:=K) ?_ (le_add_of_nonneg_left (show 0 ≤ Q.goal L x from (arable H).le))⟩
    have hh : Ac.Hit H.birth (radiusB x) (tariff g (ConnectedActivityE6.lengths T R) (fun _=>0) Q.ε) Q.relative (η*c'):=hz.hit
    refine budget_mono (budget_plus (hh i) (hz' i)) ?_ (fun t=>?_)
    · intro t; split; exact mul_nonneg (mul_nonneg (hr t) (Real.exp_pos _).le) (Real.exp_pos _).le; exact le_rfl
    split_ifs
    next h=>
      let ex v:= tariff v (ConnectedActivityE6.lengths T R) (fun _=>0) Q.ε t * Real.exp (Q.relative*coverNumber (radiusB x) (H.birth t))
      change ex r≤ ex g+ ex u
      by_cases hp:t=Daisy.sparkling c f M.turn
      · rw [show ex r=ex u from congr_arg (fun z=> z* Real.exp (2*Q.ε*(ConnectedActivityE6.lengths T R t)+0)* Real.exp (Q.relative*coverNumber (radiusB x) (H.birth t))) (show r t=u t by simp [r,u,colly,hp])]; exact le_add_of_nonneg_left (mul_nonneg (mul_nonneg (hz.nonneg t) (Real.exp_pos _).le) (Real.exp_pos _).le)
      rw [show ex r=ex g from congr_arg (fun z=> z* Real.exp (2*Q.ε*(ConnectedActivityE6.lengths T R t)+0)* Real.exp (Q.relative*coverNumber (radiusB x) (H.birth t))) (show r t=g t from if_neg hp)]
      exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (hu _) (Real.exp_pos _).le) (Real.exp_pos _).le)
    rw [zero_add]
  have hs:= Mixed.ready_vertices S Q.halo (radiusB x) R' H.birth r _ (steamP S (cR)) (pace Ξ K hC hv) hh
  let f:= Mixed.costs S Q.halo (radiusB x) (steamP S (cR)) r
  have hw : tariff (hook M H Ξ y η ζ) Ix 0 Q.ε=tariff f Ix (Mixed.stamp S R') Q.ε := by
    funext i
    unfold Reserves.tariff
    rw [show hook M H Ξ y η ζ i= Real.exp (Mixed.stamp S R' i)* f i from ?_]; swap
    · unfold hook; rw [← sparkPath]; rcases i with i|i
      · rw [if_neg (by simp)]; rfl
      unfold f; rw [show Mixed.stamp S R' (.inr i)=_ * ((0:ℕ):ℝ) from rfl,Nat.cast_zero,mul_zero,Real.exp_zero,one_mul]
      by_cases h:i=Daisy.sparkling _ _ M.turn; rw [if_pos (congr_arg Sum.inr h)]; exact (show r i = _ from if_pos h).symm
      rw [if_neg (fun hx=>h (Sum.inr.inj hx)),entryO]; exact (show r i= _ from if_neg h).symm
    simp only [Pi.zero_apply,add_zero,Real.exp_add]; ring
  rw [hw]; exact hs

-- coupon pays every partner lease. Retain marker boost even when it would otherwise be a pollutant.
def boosted (z:ℝ) (l:ℕ) (η ζ:ℝ)(p:Molecule S) :ℝ := if H.ticketsP 0 0 0 p then (∏ i∈p,hook M H Ξ z η ζ i)*(1+H.shapeW p)^l else 0
omit hI hA hK hv in
lemma hope (p:Molecule S)(l:ℕ) : 0 ≤ boosted M H Ξ y l η ζ p:=by
  unfold boosted; split
  · exact mul_nonneg (prod_nonneg fun i _=> hookN M H Ξ h hζ hp hy i) (pow_nonneg (add_nonneg zero_le_one (H.positive_volume p)) _)
  exact le_rfl
lemma desk (l:ℕ) : Ac.Hit H.unionP (radiusB x) (boosted M H Ξ y l η ζ) Q.exp
      (Reserves.extract Q.ε l 0 0 * Reserves.treeYield Sx (1/2) 0) :=by
  intro u; let Z:=H.supportP
  have he z:0≤ Ix z:=by
    rcases z with z|z; exact mul_nonneg Ξ.lives.extra (Nat.cast_nonneg _); exact Nat.cast_nonneg _
  have hc:= Reserves.sets Z _ _ Ix 0 (hookN M H Ξ h hζ hp hy) he Q.usable Q.bound (turnstile M H Ξ h hp hy hI hA hK hv) 0 l u (fun i=>H.ticketsP 0 0 0 i) (T:=0) (U:=0) (fun i _ _ _ _=> ⟨(show 0≤ H.shapeW i from H.positive_volume _),by simp⟩)
  convert hc using 1; ext i
  by_cases hp : H.ticketsP 0 0 0 i
  swap; · unfold boosted; simp only [hp, ↓reduceIte, zero_mul,false_and]; split <;> rfl
  by_cases hv : u ∈ H.unionP i
  · rw [if_pos hv,boosted, if_pos hp, if_pos ⟨hp,Nat.zero_le _⟩, Reserves.rooted, if_pos ⟨(H.attends _).1 hp,hv⟩]; unfold currency; change (_ * (1+H.shapeW i)^l)*Real.exp _= ((∏ j∈i, hook M H Ξ y η ζ j)*Real.exp (Q.exp*coverNumber _ (H.unionP i)))*(1+H.shapeW i)^l; ring
  rw [if_neg hv, if_pos ⟨hp,Nat.zero_le _⟩,Reserves.rooted,if_neg (fun h=> hv h.2),zero_mul]
end ticket
end YM.LocalTaylorR2.Marker
