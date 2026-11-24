import YM.LocalTaylorR2.Orbit.Totals
/-! Momentum & support prices accounting already earned H.Plot. Late numeric
angle capable of Theta.Tree through any Offer instant. -/
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
open Marker Charge Tender Port
local notation "V"=> Paint (restP M H p)
local notation "T₀"=> restP M H p
local notation "HG"=> H.unionP Θ
local notation "Ψ"=> Orbit.checked M H p ∧ Clear T₀
variable {j l k n:ℕ} {D K e v₀ d r z ξ x b' a' B' R' A c' θ ζ ρ:ℝ}
variable (ht: Tinted G s K d o.a L χ j) (U:StoresR2 H j v₀ d A D k x n χ)
variable (N:Captain H j b' d v₀ w A a' r B' R' (n+j) χ) (Ξ:Utopia H j v₀ d r b' χ)
variable (hB:LocalBookingsR2 ζ c' N.conduit)(h:1≤betaF G s L)(hζ:0≤ζ)(hs:1≤θ)(hp:1≤ρ)(hP:ρ*c'≤1)(hK:ρ^(l+1) ≤ betaF G s L^ζ)(hM:betaF G s L^ζ ≤ Real.exp (Q.mark L μ s))
local notation "Φ"=> N.conduit
local notation "η"=> (l+1:ℝ)*θ*ρ
local notation "γ"=> (1+H.shapeW Θ)^(n+j)
local notation "φ"=> truck D x K r l j
variable {ι:Type} [Fintype ι] (Y:ι→Leaf R) (u:ι→ℝ)(hU:YM.Merge.Palette.Plot Y H u)
open YM.Merge Palette Reserves Mixed Gas Trees
local notation "aY"=> sign Y S
local notation "E"=> Tickets aY
local notation "uY"=> wages Y u
local notation "uH"=>edit H χ (Φ) Y u (η) ζ
local notation "B"=> (radiusB s)
local notation "Sc"=> (Q.costs L μ R.beta s b')
local notation "Sd"=> (H.shapeW Θ)
local notation "Ix"=> Mixed.lengths S Sc (ConnectedActivityE6.lengths T R)
def convoy (Q: YM.ConnectedActivityE6.Target G P)(L:Side) (μ s θ c' ρ:ℝ)(l:ℕ):= current Q L μ s+ ((l+1:ℝ)*θ*ρ*c'+Q.goal L s+ribbon Q L s)
variable (hv: degreePrice (radiusB s) (convoy Q L μ s θ c' ρ l) Q.δ ≤ 1/2)
local notation "p₀"=> convoy Q L μ s θ c' ρ l
include hU h hB hs hp hv
local notation "dT"=> (steamP S (Q.costs L μ R.beta s C))
-- remove mystery.C budgets NONE of H.C needed here except for `birth` True and `Plot`; ξ lean sizes verified. photon
lemma flowPay : Ready H.supportP B (Reserves.tariff uH Ix 0 Q.ε) (Q.exp+2*Q.ε) p₀ Q.δ (1/2) := by
  let K:= (η)*c'+Q.goal L s+ribbon Q L s; let R':=higher Sc K
  let g:=raiseT (Φ) (η) ζ; let f' (q:Alphabet c f):=Tickets.extra (Palette.mark Y (c:=c)) uY q
  let b:= g+f'
  have hp' :1≤ (η):= height hs hp; have hX:= Real.rpow_nonneg (zero_le_one.trans h) (Q.rate)
  have hK : 0≤K:= add_nonneg (add_nonneg (mul_nonneg (zero_le_one.trans hp') (budget_nonneg (hB.leases.hit 0))) hX) (mul_nonneg hX (Real.exp_pos _).le)
  have hx:= Raw.boost_price hB.leases (zero_le_one.trans hp'); have hf(i):0 ≤ f' i:= sum_nonneg fun i _=> (by split; exact wagesN H Y u hU _; rfl)
  have hr := H.armed
  have hh : Accounts S Q.halo B R' H.birth b (ConnectedActivityE6.lengths T R) (steamP S Sc):=by
    refine ⟨(Φ).accrues.packetBound,fun i=>add_nonneg (hx.nonneg i) (hf i),(Φ).accrues.extra, fun i=> budget_loosen (C:=K) ?_ (le_add_of_nonneg_left hX) ⟩
    have hh : Ac.Hit H.birth B (tariff g (ConnectedActivityE6.lengths T R) (fun _=>0) Q.ε) Q.relative ((η)*c'):=hx.hit
    have h : Ac.Hit H.birth B (tariff (Palette.pitch Y H u) (ConnectedActivityE6.lengths T R) (fun _=>0) Q.ε) Q.relative (Q.goal L s+ribbon Q L s):= hU.pays.pays
    unfold K; rw [add_assoc]; refine budget_mono (budget_plus (hh i) (h i)) ?_ ?_
    · intro j; split; exact mul_nonneg (mul_nonneg (add_nonneg (hx.nonneg _) (hf _)) (Real.exp_pos _).le) (Real.exp_pos _).le; rfl
    intro j; split_ifs
    next hi=>
      let e:= Real.exp (2*(Q.ε*ConnectedActivityE6.lengths T R j)+0)*Real.exp (Q.relative*coverNumber (radiusB s) (H.birth j)); let f:=g j; let p:= f' j
      have hu:0 ≤ e:= by unfold e; positivity
      have hq:=H.armed.holds j
      change ((f+p)*Real.exp _*Real.exp _≤ f*Real.exp _*Real.exp _+(H.opt j+p)*Real.exp _*Real.exp _)
      simp only [mul_assoc]; change (f+p)*e≤ f*e+(H.opt j+p)*e; rw [add_mul]; exact add_le_add_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hq) hu) _ -- order
    rw [zero_add]
  have hK:= Mixed.ready_vertices S Q.halo B R' H.birth b _ (steamP S Sc) (Tender.pace (Φ) K hK hv) hh
  let f:= Mixed.costs S Q.halo B (steamP S Sc) b
  have hw : tariff uH Ix 0 Q.ε=tariff f Ix (Mixed.stamp S R') Q.ε := by
    funext i; unfold Reserves.tariff; have hx : uH i= Real.exp (Mixed.stamp S R' i)*f i:= by
      rcases i with i|i
      · unfold edit Tickets.extra; rw [sum_eq_zero,add_zero]; · rfl
        intro j _; exact if_neg (fun h=> by have hf:=(show .inr _ = sign Y S j from Daisy.sparkPath ..).trans h; contradiction)
      unfold edit; rw [entryO]; unfold Tickets.extra; change _= Real.exp ((Sc).markSeed*(0:ℕ))*b i; rw [Nat.cast_zero,mul_zero,Real.exp_zero,one_mul]; apply congr_arg (g i+·); refine sum_congr rfl ?_; intro j _; rw [← show Sum.inr _=sign Y S j from Daisy.sparkPath ..]; simp only [Sum.inr.injEq]; rfl
    rw [hx]; simp only [Pi.zero_apply,add_zero,Real.exp_add]; ring
  rw [hw]; exact hK
include hζ
omit hB hv in
lemma relevant (i:Molecule S) : 0 ≤ footing H χ (Φ) Y u (η) ζ (n+j) i:=by
  unfold footing; split
  · exact mul_nonneg (prod_nonneg fun i _=> feeN H χ (Φ) Y u hU _ h hζ (Orbit.height hs hp)) (pow_nonneg (add_nonneg zero_le_one (H.positive_volume _)) _)
  exact le_rfl
lemma memory : Ac.Hit H.unionP B (footing H χ (Φ) Y u (η) ζ (n+j)) Q.exp (Reserves.extract Q.ε (n+j) 0 0 * treeYield p₀ (1/2) 0):=by
  intro x
  let Y':= H.supportP; let u':= uH; let k:= n+j
  have hr z:0 ≤ Ix z:=by
    rcases z with z|z; exact mul_nonneg (Φ).lives.extra (Nat.cast_nonneg _); exact Nat.cast_nonneg _
  have hc:= Reserves.sets Y' _ u' Ix 0 (fun i=> feeN H χ (Φ) Y u hU _ h hζ (Orbit.height hs hp)) hr Q.usable Q.bound (flowPay H χ N hB h hs hp Y u hU hv) 0 k x (fun i=>H.ticketsP 0 0 0 i) (T:=0) (U:=0) (fun i _ _ _ _=> ⟨(show 0≤ H.shapeW i from H.positive_volume _),by simp⟩)
  convert hc using 1; ext i
  by_cases hp : H.ticketsP 0 0 0 i
  swap; · unfold footing; simp only [hp, ↓reduceIte, zero_mul,false_and]; split <;> rfl
  by_cases hv : x ∈ H.unionP i
  · rw [if_pos hv,footing, if_pos hp, if_pos ⟨hp,Nat.zero_le _⟩, Reserves.rooted, if_pos ⟨(H.attends _).1 hp,hv⟩]; unfold u' currency; change (_ * (1+H.shapeW i)^k)*Real.exp _= ((∏ j∈i, edit _ _ _ _ _ _ _ j)*Real.exp (Q.exp*coverNumber _ (H.unionP i)))*(1+H.shapeW i)^k; ring
  rw [if_neg hv, if_pos ⟨hp,Nat.zero_le _⟩,Reserves.rooted,if_neg (fun h=> hv h.2),zero_mul]

include U ht
abbrev forecast (Q: YM.ConnectedActivityE6.Target G P)(L:Side) (μ s θ c' ρ x D K r:ℝ)(l n j:ℕ) := 2^j*(truck D x K r l j*(Reserves.extract Q.ε (n+j) 0 0 * treeYield (convoy Q L μ s θ c' ρ l) (1/2) 0))
lemma incarnate {a:ℝ} (ha:a ≤ Q.exp): Ac.Hit H.smallAt B (fun i=>2^j* totalBill H χ i N Y u K D θ ζ x ρ l) a (forecast Q L μ s θ c' ρ x D K r l n j):=by
  apply AnalyticBridge.VerifiedReset.Quotes.hit_scale (by positivity : 0 ≤ (2:ℝ)^j)
  have he:0≤ φ:= by unfold truck speedS; have h:= (Φ).active; have h':= Tinted.salt ht; have hX:= U.sure; have hd:= U.fuel; positivity
  have hz:= AnalyticBridge.VerifiedReset.Quotes.hit_scale he (memory H χ N hB h hζ hs hp Y u hU hv); intro i; have hv:= budget_pull (fun i:H.ThinP=> i.val) Subtype.val_injective (hz i); apply budget_mono hv ?_ ?_
  · intro j; split
    next=> exact mul_nonneg (totalN H χ _ ht U N h hζ hs hp Y u hU) (Real.exp_pos _).le
    exact le_rfl
  intro j; dsimp only; split
  next hh=>
    rw [if_pos (show i∈H.unionP j.val from hh)]
    exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _))) (totalN H χ _ ht U N h hζ hs hp Y u hU)
  exact hv.1 j
end YM.LocalTaylorR2.Orbit
