import YM.LocalTaylorR2.Tolls
/-!
# An absolute two-level cluster ticket. Actual geometric leased weights
applied to all optional alphabets. Extra mark extraction on ALL packet
vertices. Here use only the first tree; the second will subtract in the
transported Log representation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2
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
namespace Tender
-- Raise optional hit budget. The new degreePrice criterion checked separately; seed/packet price unchanged.
def higher (a:Mixed.Costs) (K:ℝ) : Mixed.Costs := {a with rootHit:=a.rootHit+K, optionalHit:=a.optionalHit+K}
lemma supply {B l:ℕ} (a:Mixed.Costs) {K:ℝ} (hx:a.Buy L l B) (hK:0≤K) (hv: degreePrice B (a.rootHit+K) a.reserveTree ≤ a.q): (higher a K).Buy L l B := by
  refine ⟨hx.eps,hx.δ,add_pos_of_pos_of_nonneg hx.γ hK,hx.capture,hx.extra,hx.marked,hx.price,hx.packet,?_ ,hv,hx.grows⟩
  exact le_trans (add_assoc _ _ _).symm.le (add_le_add_left hx.combined _)

variable {j k n l : ℕ} {v r d A D x C' ζ η c' : ℝ} {χ : Chi}
variable (Ξ:Utopia H j v d r C' χ)
-- Stamp basis both in Curtain and numerical mark rate
local notation "cR" => Q.costs L μ R.beta s C'
abbrev current (Q: YM.ConnectedActivityE6.Target G P) (L:Side) (μ s:ℝ) := (Q.costs L μ 1 s 0).rootHit

-- z = power ζ plus marker bump. Compare prices BEFORE support conversion

def raiseT (η ζ:ℝ) (i:Alphabet c f):ℝ:= η*(betaF G s L^lease ζ c f i * Ξ.flair i)

def entry (η ζ:ℝ) (i:Head S):ℝ:= Real.exp (Mixed.stamp S (cR) i) * Mixed.costs S Q.halo (radiusB s) (steamP S (cR)) (raiseT Ξ η ζ) i

include Ξ
lemma pace (K:ℝ) (hK:0≤ K) (hv: degreePrice (radiusB s) ((current Q L μ s)+ K) Q.δ ≤ 1/2):
    (higher (cR) K).Buy S.patch.L Q.halo (radiusB s) := supply _ Ξ.lives hK hv -- incl

lemma entryO (η ζ:ℝ) (i:ConnectedActivityE6.Alphabet c f) : entry Ξ η ζ (.inr i)=raiseT Ξ η ζ i:=by
  unfold entry; rw [show Mixed.stamp S (cR) (.inr i)= (cR).markSeed*↑(0:ℕ) from rfl,Nat.cast_zero,mul_zero,Real.exp_zero,one_mul]; rfl
lemma entryP (η ζ:ℝ) (i : Stores S) : entry Ξ η ζ (.inl i) = Real.exp ((cR).markSeed*i.shares)*Ξ.fare (.inl i):=rfl
lemma cheap (h : 1≤betaF G s L) (hζ:0≤ζ) (hp:1≤η) (i:Head S) : Ξ.fare i≤entry Ξ η ζ i := by
  rcases i with i|i
  · rw [entryP]; exact le_mul_of_one_le_left (Ξ.fares _) (Real.one_le_exp (mul_nonneg Ξ.lives.marked (Nat.cast_nonneg _)))
  rw [entryO]
  exact le_trans (le_mul_of_one_le_left (show 0≤Ξ.flair i from Ξ.uses.nonneg _) (Real.one_le_rpow h (leaseNN hζ i)))
    (le_mul_of_one_le_left (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans h) _) (Ξ.uses.nonneg _)) hp)
lemma polluter_cost (h : 1≤betaF G s L) (hp:1 ≤ η) (U:Molecule S) (he:troupe T R Q.halo (radiusB s) U) (hl: betaF G s L^ζ ≤ Real.exp ((cR).markSeed)) {i:Head S} (hi:i∈U) (hd : ¬Drain i):
    (betaF G s L^ζ)*Ξ.fare i≤ entry Ξ η ζ i:=by
  let u:=betaF G s L
  rcases i with i | i | i | i
  · have hh : 1 ≤ i.shares:= by rw [← Packets.seeds_card]; exact Finset.card_pos.mpr (he.1.checkpoints i (mem_toLeft.mpr hi)).1
    rw [entryP]; exact mul_le_mul_of_nonneg_right (hl.trans (Real.exp_monotone (le_mul_of_one_le_right Ξ.lives.marked (by exact_mod_cast hh)))) (Ξ.fares _)
  all_goals rw [entryO]
  · exact le_mul_of_one_le_left (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans h) _) (Ξ.fares _)) hp
  · unfold raiseT; have hz:slowLog c f i≠0:=fun h=> hd ⟨i,rfl,h⟩
    rw [show lease ζ c f (.inr (.inl i))=ζ from leaseHigh hz]
    exact le_mul_of_one_le_left (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans h) _) (Ξ.fares _)) hp
  exact le_mul_of_one_le_left (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans h) _) (Ξ.fares _)) hp

section ticket
variable (h : 1≤betaF G s L) (hζ:0≤ζ) (hp:1≤η) (hI:LocalBookingsR2 ζ c' Ξ)
  (hv: degreePrice (radiusB s) ((current Q L μ s) + η*c') Q.δ ≤ 1/2)
local notation "Ix" => Mixed.lengths S (cR) (ConnectedActivityE6.lengths T R)
include h hζ hp hI hv
-- actual momentum thresholds. all lengths retained
omit hζ in
lemma hurdle : Ready H.supportP (radiusB s) (Reserves.tariff (entry Ξ η ζ) Ix 0 Q.ε)
    (Q.exp+2*Q.ε) ((current Q L μ s)+η*c') Q.δ (1/2) := by
  let K:= η*c'; let R':=higher (cR) K; let g:=raiseT Ξ η ζ
  have hK : 0≤K:= mul_nonneg (zero_le_one.trans hp) (budget_nonneg (hI.leases.hit 0))
  have hz:= Raw.boost_price hI.leases (zero_le_one.trans hp)
  have hx : Mixed.Accounts S Q.halo (radiusB s) R' H.birth g (ConnectedActivityE6.lengths T R) (steamP S (cR)) := by
    refine ⟨Ξ.accrues.packetBound,hz.nonneg,Ξ.accrues.extra,fun i=> budget_loosen (hz.hit i) (le_add_of_nonneg_left ?_)⟩
    exact Real.rpow_nonneg (zero_le_one.trans h) _
  have ht:= Mixed.ready_vertices S Q.halo (radiusB s) R' H.birth g _ (steamP S (cR)) (pace Ξ K hK hv) hx
  -- consume stamp of actual cost
  let f:= Mixed.costs S Q.halo (radiusB s) (steamP S (cR)) g
  have hw : tariff (entry Ξ η ζ) Ix 0 Q.ε=tariff f Ix (Mixed.stamp S R') Q.ε := by
    funext i; unfold tariff entry
    simp only [Pi.zero_apply,add_zero,Real.exp_add]
    change Real.exp _ * f i*Real.exp _ = f i*(Real.exp _ * Real.exp (Mixed.stamp S (cR) i)); ring
  rw [hw]; exact ht

def advantage (η ζ:ℝ) (l:ℕ) (U:Molecule S) := if H.ticketsP 0 0 0 U then (∏ i∈ U, entry Ξ η ζ i)*(1+H.shapeW U)^l else 0
omit hI hv in
lemma pos (l:ℕ) (U:Molecule S): 0 ≤ advantage Ξ η ζ l U:=by
  unfold advantage; split
  · exact mul_nonneg (prod_nonneg fun i _=> (Ξ.fares _).trans (cheap Ξ h hζ hp i)) (pow_nonneg (add_nonneg zero_le_one (H.positive_volume U)) _)
  exact le_rfl
lemma sheet (l:ℕ) : Ac.Hit H.unionP (radiusB s) (advantage Ξ η ζ l) Q.exp (Reserves.extract Q.ε l 0 0 * Reserves.treeYield ((current Q L μ s)+η*c') (1/2) 0) := by
  intro x; let u:=entry Ξ η ζ; let Z:=H.supportP
  have hr z:0 ≤ Ix z:=by
    rcases z with z|z; exact mul_nonneg Ξ.lives.extra (Nat.cast_nonneg _); exact Nat.cast_nonneg _
  have hc:= Reserves.sets Z _ u Ix 0 (fun i=> (Ξ.fares i).trans (cheap Ξ h hζ hp i)) hr Q.usable Q.bound (hurdle Ξ h hp hI hv) 0 l x (fun i=>H.ticketsP 0 0 0 i) (T:=0) (U:=0) (fun i _ _ _ _=> ⟨(show 0≤ H.shapeW i from H.positive_volume _),by simp⟩)
  convert hc using 1; ext i
  by_cases hp : H.ticketsP 0 0 0 i
  swap; · unfold advantage; simp only [hp, ↓reduceIte, zero_mul,false_and]; split <;> rfl
  by_cases hv : x ∈ H.unionP i
  · rw [if_pos hv,advantage, if_pos hp, if_pos ⟨hp,Nat.zero_le _⟩, Reserves.rooted, if_pos ⟨(H.attends _).1 hp,hv⟩]; unfold u currency; change (_ * (1+H.shapeW i)^l)*Real.exp _= ((∏ j∈i, entry Ξ η ζ j)*Real.exp (Q.exp*coverNumber _ (H.unionP i)))*(1+H.shapeW i)^l; ring
  rw [if_neg hv, if_pos ⟨hp,Nat.zero_le _⟩,Reserves.rooted,if_neg (fun h=> hv h.2),zero_mul]
end ticket
end Tender
end YM.LocalTaylorR2
