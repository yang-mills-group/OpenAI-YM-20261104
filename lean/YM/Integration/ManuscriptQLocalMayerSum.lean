import YM.RGLocalTaylor.Laminate.Land
import YM.RGLocalTaylor.Retain.Stencil

/-!
# Rooted sum of the complete signed healthy Gaussian comparisons

Each retained component uses the physical decoration profile and its entire marked team.
The extra factor counting Gaussian positions is paid at the same original coverage exponent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalMayerSum
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt Blaze.March
open RGLocalTaylor RGLocalTaylor.Mayer RGLocalTaylor.Laminate RG01.Survive Trees YM.Merge Palette
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {j M : ℕ} {R : Rep G f} {s μ C W v d r C' θ K ρ : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R} {Ξ : Utopia H j v d r C' χ}

private theorem remainingBlaze (A : Team R) (p : Molecule S) : blaze (p \ A.signs S) = blaze p := by
  have ht : ∀ i, Sum.inr (.inr (.inr i)) ∉ A.signs S := by
    intro i hi
    exact Finset.notMem_empty i (support_eq hi ▸
      (show i∈blaze ({Sum.inr (.inr (.inr i))} : Molecule S) from
        mem_toRight.mpr (mem_toRight.mpr (mem_toRight.mpr (mem_singleton_self _)))))
  ext i
  simp only [blaze,mem_toRight,Finset.mem_sdiff,ht,and_true,not_false_eq_true]

private theorem clearBlaze (A : Team R) (p : Molecule S) (h : Start (p \ A.signs S)) :
    blaze p=∅ := by
  have hv := remainingBlaze A p
  exact hv ▸ RGLocalTaylor.Retain.goodK.chance h

def decorated (A : Team R) (p : Molecule S) (Ξ : Utopia H j v d r C' χ)
    (θ ρ : ℝ) (M : ℕ) : ℝ :=
  ∑ u : Decors (p \ A.signs S) M,
    tariff Ξ p θ u (coverWeight A S) * ρ^decorOrder u

theorem signed_team (A : Team R) (p : Molecule S) (he : Approved K θ j M)
    (hρ : 1≤ρ) (hr : ρ*Q.goal L s≤1)
    (hx : A.signs S⊆p) (h : Start (p \ A.signs S)) :
    0≤decorated A p Ξ θ ρ M ∧ decorated A p Ξ θ ρ M ≤
      A.weight*(∏ i∈p \ A.signs S, Ξ.fare i)*spreadRate M θ ρ^p.card := by
  classical
  let z:=p \ A.signs S
  have hw (i) (hi:i∈p \ z) : 0≤coverWeight A S i :=
    (partnerFit (H:=H) (j:=j) (i:=i) (compartments A p hx ▸ hi)).2
  have hp : 0≤ρ := zero_le_one.trans hρ
  have scaled : hitFace Ξ p z (coverWeight A S) * Ξ.rad^(blaze p).card =
      A.weight * ∏ i∈z, Ξ.fare i := by
    dsimp only [z]
    unfold hitFace
    rw [Ξ.remixes, remainingBlaze, compartments A p hx, coverTotal, mul_assoc]
  have base : hitFace Ξ p z (coverWeight A S) = A.weight * ∏ i∈z, Ξ.fare i := by
    simpa only [clearBlaze A p h, Finset.card_empty, pow_zero, mul_one] using scaled
  have hc : 0≤ A.weight*(∏ i∈z,Ξ.fare i) := mul_nonneg A.profit (prod_nonneg fun i _=>Ξ.fares i)
  constructor
  · exact sum_nonneg fun u _=>mul_nonneg (tariff_nonneg he hw u) (pow_nonneg hp _)
  calc
    decorated A p Ξ θ ρ M ≤ ∑ _u : Decors z M, hitFace Ξ p z (coverWeight A S)*(θ*ρ)^z.card := by
      exact sum_le_sum fun u _=>price_cauchy (Ξ:=Ξ) he hp hr hw h u
    _ = A.weight*(∏ i∈z,Ξ.fare i)*spreadRate M θ ρ^z.card := by
      rw [base]; simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      simp only [Decors,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe]
      push_cast
      simp only [spreadRate, mul_pow, add_comm (M : ℝ) 1]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (spread_pos hρ he.nonneg) (Finset.card_le_card Finset.sdiff_subset)) hc

variable {ι : Type} [Fintype ι] (M' : ι→Leaf R) (w : ι→ℝ)

def aggregate (p : Molecule S) (Ξ : Utopia H j v d r C' χ) (θ ρ : ℝ) (M : ℕ) : ℝ :=
  ∑ k : Tickets (Palette.sign M' S), packPrice w k.val *
    if authorized H p ∧ (Palette.team M' k).signs S⊆p ∧ Start (p \ (Palette.team M' k).signs S) then
      H.shapeW p*decorated (Palette.team M' k) p Ξ θ ρ M else 0

private theorem scalarCharge {x y cost mark power : ℝ} (hxy : x ≤ y) (hc : 0 ≤ cost)
    (hy : 0 ≤ y) (hm : 1 ≤ mark) (hp : 0 ≤ power) :
    x * (cost * power) ≤ cost * y * mark * power := by
  calc
    x * (cost * power) = (cost * x) * power := by ring
    _ ≤ (cost * y) * power := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxy hc) hp
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (mul_nonneg hc hy) hm) hp

private theorem singleCharge (A : Team R) (p : Molecule S) (he : Approved K θ j M)
    (hρ : 1 ≤ ρ) (hr : ρ * Q.goal L s ≤ 1) :
    (if authorized H p ∧ A.signs S ⊆ p ∧ Start (p \ A.signs S) then
      H.shapeW p * decorated A p Ξ θ ρ M else 0) ≤ Laminate.invoice A p Ξ θ ρ 0 0 1 M 1 := by
  classical
  have shape := H.positive_volume p
  have growth : 1 ≤ spreadRate M θ ρ := spread_pos hρ he.nonneg
  have hc : 0≤ A.weight*(∏ i∈p \ A.signs S,Ξ.fare i) := mul_nonneg A.profit (prod_nonneg fun i _=>Ξ.fares i)
  have hv : H.shapeW p ≤ (1+H.shapeW p)^(1+j) :=
    calc
      H.shapeW p ≤ 1 + H.shapeW p := by linarith
      _ = (1 + H.shapeW p)^1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith only [shape]) (by omega)
  have hm := marking_ge H p
  have zero : 0≤ A.weight*(∏ i∈p \ A.signs S,Ξ.fare i)*(1+H.shapeW p)^(1+j) :=
    mul_nonneg hc (pow_nonneg (by linarith) _)
  by_cases ha : authorized H p ∧ A.signs S⊆p
  · unfold Laminate.invoice budCost
    rw [if_pos ha]
    simp only [speedBill,mul_zero,add_zero,one_pow,one_mul]
    by_cases hs : Start (p \ A.signs S)
    · rw [if_pos ⟨ha.1,ha.2,hs⟩]
      have hu := (signed_team A p (Ξ:=Ξ) he hρ hr ha.2 hs).2
      calc
        _ ≤ H.shapeW p*(A.weight*(∏ i∈p \ A.signs S,Ξ.fare i)*spreadRate M θ ρ^p.card) :=
          mul_le_mul_of_nonneg_left hu shape
        _ ≤ _ := scalarCharge hv hc (pow_nonneg (by linarith only [shape]) _) hm
          (pow_nonneg (zero_le_one.trans growth) _)
    · rw [if_neg fun hh=>hs hh.2.2]
      exact mul_nonneg (mul_nonneg zero (zero_le_one.trans hm)) (pow_nonneg (zero_le_one.trans growth) _)
  · rw [if_neg fun hh=>ha ⟨hh.1,hh.2.1⟩]
    exact le_of_eq (by simp [Laminate.invoice,ha])

private theorem quoted (hP : Palette.Plot M' H w) (he : Approved K θ j M)
    (hρ : 1≤ρ) (hr : ρ*Q.goal L s≤1) (p : Molecule S) :
    0≤aggregate M' w p Ξ θ ρ M ∧ aggregate M' w p Ξ θ ρ M ≤
      launchFoot M' w Ξ p θ ρ 0 0 1 M 1 := by
  classical
  have hmoney (k : Tickets (Palette.sign M' S)) : 0≤packPrice w k.val :=
    prod_nonneg fun i _=>hP.live i
  have shape:=H.positive_volume p
  constructor
  · apply sum_nonneg
    intro k hk
    apply mul_nonneg (hmoney k)
    split
    next hs => exact mul_nonneg shape (signed_team _ p he hρ hr hs.2.1 hs.2.2).1
    exact le_rfl
  unfold aggregate launchFoot
  apply sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_left _ (hmoney k)
  exact singleCharge (Palette.team M' k) p he hρ hr

theorem rooted (hP : Palette.Plot M' H w) (he : Approved K θ j M)
    (hρ : 1≤ρ) (hr : ρ*Q.goal L s≤1)
    (hbase : degreePrice (radiusB s) (width Q μ L s) Q.δ≤1/2)
    (hs : degreePrice (radiusB s) (spreadRate M θ ρ*width Q μ L s) Q.δ≤1/2) :
    Ac.Hit H.unionP (radiusB s) (fun p=>aggregate M' w p Ξ θ ρ M) Q.exp
      (first_price Q L μ s (1+j) (spreadRate M θ ρ)) := by
  classical
  let E:=Mixed.lengths S (Q.costs L μ R.beta s C') (ConnectedActivityE6.lengths T R)
  have hE i : 0≤ E i := by
    rcases i with i|i
    · exact mul_nonneg Ξ.lives.extra (Nat.cast_nonneg _)
    · exact Nat.cast_nonneg _
  let f:=projectedWeight M' w Ξ
  have price:=paid_mark H f E (projected_pos M' w Ξ hP) hE
    (rich M' w Ξ hP hbase) (zero_lt_one.trans_le (spread_pos hρ he.nonneg)) (fun i=>rfl) hs (1+j)
  intro x
  apply budget_mono (price x)
  · intro p
    split
    next hp=> exact mul_nonneg (quoted M' w (Ξ:=Ξ) hP he hρ hr p).1 (Real.exp_pos _).le
    exact le_rfl
  intro p
  split
  next _ =>
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    change aggregate M' w p Ξ θ ρ M ≤ (if H.ticketsP 0 0 0 p then
      (∏ i ∈ p, f i) * (1 + H.shapeW p)^(1+j) else 0) * marking H p * spreadRate M θ ρ^p.card
    by_cases ha : authorized H p
    · rw [if_pos ((H.attends p).2 ha.1)]
      have hh:= (quoted M' w (Ξ:=Ξ) hP he hρ hr p).2
      rw [layerFull M' w Ξ p ha] at hh
      simpa only [speedBill,mul_zero,add_zero,one_pow,one_mul] using hh
    · have hz : aggregate M' w p Ξ θ ρ M=0 := by
        unfold aggregate
        simp only [ha,false_and,↓reduceIte,mul_zero,sum_const_zero]
      rw [hz]
      exact mul_nonneg (mul_nonneg (by split <;> first | exact le_rfl |
        exact mul_nonneg (prod_nonneg fun i _=>projected_pos M' w Ξ hP i) (pow_nonneg (by linarith [H.positive_volume p]) _))
        (zero_le_one.trans (marking_ge H p))) (pow_nonneg (zero_le_one.trans (spread_pos hρ he.nonneg)) _)
  next _=>exact le_rfl


variable {E : Type*} [NormedAddCommGroup E]

/-- The signed Gaussian difference for each complete marked molecule may be tested
against its own source before taking the rooted sum. -/
theorem tested (hP : Palette.Plot M' H w) (he : Approved K θ j M)
    (hρ : 1≤ρ) (hr : ρ*Q.goal L s≤1)
    (hbase : degreePrice (radiusB s) (width Q μ L s) Q.δ≤1/2)
    (hs : degreePrice (radiusB s) (spreadRate M θ ρ*width Q μ L s) Q.δ≤1/2)
    (D : (p : Molecule S) → (k : Tickets (Palette.sign M' S)) →
      Decors (p \ (Palette.team M' k).signs S) M → E)
    {C₀ : ℝ} (hC : 0≤C₀)
    (hD : ∀ p k, authorized H p → (Palette.team M' k).signs S⊆p →
      Start (p \ (Palette.team M' k).signs S) → ∀ u,
        ‖D p k u‖ ≤ C₀ * H.shapeW p * tariff Ξ p θ u (coverWeight (Palette.team M' k) S)) :
    Ac.Hit H.unionP (radiusB s) (fun p=> ∑ k : Tickets (Palette.sign M' S),
      packPrice w k.val *
        if authorized H p ∧ (Palette.team M' k).signs S⊆p ∧ Start (p \ (Palette.team M' k).signs S) then
          ∑ u, ‖D p k u‖ * ρ^decorOrder u else 0)
      Q.exp (C₀*first_price Q L μ s (1+j) (spreadRate M θ ρ)) := by
  classical
  have hw (k : Tickets (Palette.sign M' S)) : 0≤ packPrice w k.val :=
    prod_nonneg fun i _=>hP.live i
  have hpos := (zero_le_one.trans hρ)
  intro x
  have base:=budget_scale hC (rooted M' w hP he hρ hr hbase hs (Ξ:=Ξ) x)
  apply budget_mono base
  · intro p
    split
    next hp =>
      apply mul_nonneg _ (Real.exp_pos _).le
      apply sum_nonneg
      intro k hk
      apply mul_nonneg (hw k)
      split
      · exact sum_nonneg fun u _=>mul_nonneg (norm_nonneg _) (pow_nonneg hpos _)
      exact le_rfl
    exact le_rfl
  intro p
  dsimp only
  by_cases hx : x∈H.unionP p
  · rw [if_pos hx,if_pos hx,←mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    unfold aggregate
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    by_cases h : authorized H p ∧ (Palette.team M' k).signs S⊆p ∧ Start (p \ (Palette.team M' k).signs S)
    · rw [if_pos h,if_pos h,mul_left_comm C₀]
      apply mul_le_mul_of_nonneg_left _ (hw k)
      unfold decorated
      rw [←mul_assoc,mul_sum]
      apply sum_le_sum
      intro u hu
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_right (hD p k h.1 h.2.1 h.2.2 u) (pow_nonneg hpos _)
    · rw [if_neg h,if_neg h,mul_zero,mul_zero]
  · simp only [if_neg hx,mul_zero,le_rfl]

/-- The actual paid half-degree tree condition bounds the remaining rooted tree sum
by a scalar chosen with the target, before its aperture or finite physical period. -/
theorem ceiling {ε γ δ : ℝ} (B k : ℕ) (hε : 0<ε) (hγ : 0≤γ) (hδ : 0<δ)
    (h : Trees.degreePrice B γ δ≤1/2) :
    Reserves.extract ε (1+k) 0 0*Reserves.treeYield γ (1/2) 0 ≤
      Reserves.extract ε (1+k) 0 0*(δ/4) := by
  have hball : (1:ℝ)≤(Animals.ballCost B:ℝ) := by
    exact_mod_cast Animals.neighbors_ge B
  have hmul : γ≤(Animals.ballCost B:ℝ)*γ := by simpa using mul_le_mul_of_nonneg_right hball hγ
  have hr : 4*((Animals.ballCost B:ℝ)*γ)/δ≤1/2 := by
    simpa only [Trees.degreePrice,Trees.stretch,mul_div_assoc] using h
  have hd := (div_le_iff₀ hδ).mp hr
  have hy : Reserves.treeYield γ (1/2) 0 ≤ δ/4 := by
    norm_num [Reserves.treeYield]
    linarith
  exact mul_le_mul_of_nonneg_left hy (by unfold Reserves.extract Reserves.polyPrice; positivity)

end YM.Integration.ManuscriptQLocalMayerSum
