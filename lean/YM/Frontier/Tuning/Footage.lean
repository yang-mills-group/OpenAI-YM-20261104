import YM.Frontier.Tuning.AngularReceipt
/-!
# Per-support mass of the complete held-word integrand. Same catastrophe event and
separate packet slots at each size, only polynomial deriv scale and one half-shape
spent on tilt costs. Burst-free estimates integrated later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.Footage
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Blaze Silica Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Clutch Matter PhysicalNext.Repeat.Alabaster PhysicalNext.Repeat.Height Held ClockShift TwoMotion AngularReceipt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R A : Rep G f} {X : Coat T F} {x :Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {z:E}
variable {H0 a C α Z β γ d η ε σ W s b μ r p q v : ℝ} {j n l : ℕ} {Q : ConnectedActivityE6.Target G P}
variable {o : Target.Order G W}
variable {χ:Chi}
local notation "b₁" => betaF G s L
local notation "M₀" => radiusB s
set_option maxRecDepth 8192
set_option pp.proofs false
set_option maxHeartbeats 1200000

variable {H: Cash W s μ L Q o H0 T R}
variable (P' : Pocket H A j v q C α d γ χ)
lemma shares_bound (S:StepData c f) (b a : ℕ) (Z:Stores S): (Z.shares : ℝ) ≤ #(Z.dome (b*a)) * (Packets.typesAt S.patch.L : ℝ):= by
 suffices h : Z.shares ≤ (Packets.homes S (Z.dome (b*a))).card by exact_mod_cast (h.trans (Packets.homes_card ..))
 rw [← Packets.seeds_card S]; apply Finset.card_le_card; intro i hi; exact mem_filter.mpr ⟨mem_univ _, halo_subset _ _ (by rw [← Packets.place_reads S]; exact mem_biUnion.mpr ⟨i,hi,Packets.contains S i⟩)⟩
open Packets
abbrev shineF (_P':Pocket H A j v q C α d γ χ) := 1+j.factorial*γ
def stepspeed (_P':Pocket H A j v q C α d γ χ) (τ : ℂ) : Head S→ℝ := Sum.elim (fun p=> phaseSpeed τ j γ α p+1) (fun i=>d*twigs R T M₀ Q.halo i)
section lump

def lumpSum (s α d γ : ℝ) (j:ℕ) (L:Side) (τ:ℂ):ℝ:=4*(d+1+(1+(j.factorial:ℝ)*γ)*(1+|α| * |τ.im| * (Animals.ballCost (radiusB s) * Packets.typesAt L : ℝ)))
-- exact shape allowance, no constants depending on whole lattice
lemma shellCost (p:Molecule S)(hp:troupe T R Q.halo M₀ p) (τ:ℂ):∑ i∈p, stepspeed P' τ i ≤ lumpSum s α d γ j L τ * H.shapeW p := by
 have h:= Utopia.worthy (H:=H) p hp
 let f0 i:= spanW T R M₀ Q.halo i
 have he (i:Head S) :0≤f0 i:=by rcases i with i|i; exact zero_le_one; exact add_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
 have hp' : ∑ i∈p,f0 i= (Finset.card p.toLeft:ℝ) + ∑ i∈p.toRight, f0 (.inr i) :=by
   have hs: (∑ i∈p.toLeft,f0 (.inl i))+(∑ i∈p.toRight,f0 (.inr i))=∑ i∈p,f0 i:=by rw [← Finset.sum_disjSum p.toLeft p.toRight f0,Finset.toLeft_disjSum_toRight]
   rw [← hs]; apply congr_arg (· + _); change (∑ i∈p.toLeft,(1:ℝ)) = _; rw [Finset.sum_const,nsmul_eq_mul,mul_one]
 change (∑ i∈p,f0 i) ≤ _ at h
 rw [hp'] at h
 let A:= Q.halo; let B:ℝ:= Animals.ballCost M₀; let y:ℝ:= H.shapeW p
 let g i:= ((H.supportP i).card:ℝ)
 have hs p': (g (.inl p'))= #(p'.dome (A*M₀)):= rfl
 have hh i: g i≤ (coverNumber M₀ (H.supportP i):ℝ)*B :=by unfold g B; exact_mod_cast (Blaze.brood (H.supportP i) M₀)
 have hc : (∑ i∈p,g i)≤ y*B:=by
   unfold y Cash.shapeW Mixed.charges Reserves.setPrice; rw [sum_mul]; apply sum_le_sum; intro i hi; refine (hh i).trans ?_; have ht: 0≤Mixed.lengths S H.faresP (ConnectedActivityE6.lengths T R) i:=by rcases i with j|j; exact mul_nonneg H.laws.acquired.extra (Nat.cast_nonneg _); exact Nat.cast_nonneg _
   exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right ht) (Nat.cast_nonneg _)
 have hγ:1≤1+j.factorial*γ:=le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans P'.strong))
 let t:ℝ:=Packets.typesAt L
 have ht: (∑ i∈p.toLeft,g (.inl i)) * t≤ y*(B*t):= by
    calc
     _ ≤ (∑ i∈p,g i)*t := mul_le_mul_of_nonneg_right ?H (by unfold t; positivity)
     _ ≤ (y*B)*t := by gcongr
     _ = _ := mul_assoc ..
    case H=>
      exact (le_add_of_nonneg_right (Finset.sum_nonneg (s:=p.toRight) (f:=fun i=>g (.inr i)) fun i _=> Nat.cast_nonneg _)).trans_eq (by rw [← Finset.sum_disjSum p.toLeft p.toRight g,Finset.toLeft_disjSum_toRight])
 have hw: ∑ i∈p.toLeft,(i.shares:ℝ) ≤ y*(B*t):=by
    refine ht.trans' ?_; rw [sum_mul]; apply sum_le_sum;intro i _; refine (shares_bound S A M₀ i).trans ?_; unfold t; rw [hs,H.laws.data.funds.length_eq]
 have hY:0≤y:= H.positive_volume _; have hd:d≥1:=P'.wide
 nth_rw 1 [← Finset.toLeft_disjSum_toRight (u:=p)];rw [Finset.sum_disjSum]
 unfold stepspeed phaseSpeed; simp only [Sum.elim, Finset.sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,← Finset.mul_sum]; unfold lumpSum
 change (1+(j.factorial:ℝ)*γ)*((Finset.card p.toLeft:ℝ) + |τ.im| * (|α| * ∑ i∈p.toLeft,(i.shares:ℝ))) + (Finset.card p.toLeft:ℝ) + d*(∑ i∈p.toRight,f0 (.inr i)) ≤ 4*(d+1+(1+(j.factorial:ℝ)*γ)*(1+|α| *|τ.im| *(B*t)))*y
 let C:= |τ.im| *|α|; have hs0:0≤C:=by unfold C; positivity
 have hx (c:ℝ)(hc:0≤c) :c≥(Finset.card p.toLeft:ℝ) →c≥∑ i∈p.toRight,f0 (.inr i)→ (1+(j.factorial:ℝ)*γ)*((Finset.card p.toLeft:ℝ) + C*∑ i∈p.toLeft,(i.shares:ℝ))+(Finset.card p.toLeft:ℝ) +d*(∑ i∈p.toRight,f0 (.inr i)) ≤ (1+j.factorial*γ)*(c+C*(y*(B*t)))+c+d*c:=fun h1 h2=>by gcongr
 rw [← mul_assoc |τ.im|,mul_comm |α| |τ.im|]; refine (hx (2*y) (mul_nonneg (by norm_num) hY) (le_trans (le_add_of_nonneg_right (Finset.sum_nonneg fun i _=> he (.inr i))) h) ((le_add_of_nonneg_left (Nat.cast_nonneg _)).trans h)).trans ?_; unfold C
 have hb: |τ.im| *|α| *(B*t) ≥0:=by unfold B t; positivity
 nlinarith only [mul_nonneg (mul_nonneg (zero_le_one.trans hγ) hb) hY,mul_nonneg (zero_le_one.trans hd) hY,mul_nonneg (zero_le_one.trans hγ) hY,hY]
end lump

def tag (P':Pocket H A j v q C α d γ χ) (r :ℝ) := stout S Q.halo M₀ (Q.costs L μ (b₁/2) s C) P'.kCost P'.logCost ((topStorm S.patch+1)*r)
lemma positive (ht:0≤r)(i : Head S) :0≤ tag P' r i:=by 
 rcases i with i|i|i|i
 · unfold tag stout Mixed.costs; dsimp only [Sum.elim];split
   next h=> exact (P'.accounts.packetBound _ h).1
   exact le_rfl
 · exact P'.accounts.holds (.inl i)
 · exact P'.accounts.holds (.inr (.inl i))
 exact mul_nonneg (add_nonneg (zero_le_one.trans (topStorm_one _)) zero_le_one) ht
lemma paid_event (p:Molecule S): (∏ i∈p,tag P' P'.rad i)=(∏ i∈p,tag P' 1 i)*P'.rad^(blaze p).card:=by
  rw [cumulate p,cumulate p];
  let Ξ:=P'; let P:=p.toRight
  have hp : (∏ i ∈ p.toLeft, tag P' P'.rad (.inl i))=∏ i∈p.toLeft, tag P' 1 (.inl i) := prod_congr rfl fun i _=> rfl
  have hs: (∏ i∈P,tag P' P'.rad (.inr i))=(∏ i∈P, tag P' 1 (.inr i))*P'.rad^(blaze p).card := by
    rw [cumulate P,cumulate P]
    let f i:= tag P' P'.rad (.inr (.inr i)); let g i:=tag P' 1 (.inr (.inr i)); let M:=topStorm S.patch+1
    change (∏ i∈ P.toLeft, Ξ.kCost i)* (∏ i∈P.toRight, f i)= ((∏ i∈ P.toLeft, Ξ.kCost i)* (∏ i∈P.toRight,g i))*_
    rw [mul_assoc,cumulate P.toRight f,cumulate P.toRight g]; apply congrArg
    change (∏ i∈ P.toRight.toLeft, Ξ.logCost i)*(∏ _i ∈ blaze p, M*Ξ.rad)=((∏ i∈ P.toRight.toLeft, Ξ.logCost i)*(∏ _i∈ blaze p, M*1))*_
    rw [Finset.prod_const,Finset.prod_const,mul_pow,mul_assoc,mul_one]
  rw [hp,hs,mul_assoc]
end YM.Frontier.Tuning.Footage
