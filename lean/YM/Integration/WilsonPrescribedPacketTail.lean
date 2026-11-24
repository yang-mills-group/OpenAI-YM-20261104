import YM.Integration.LocalComparisonUniformModelPrice
import YM.Next.RANK.Exponential
import YM.Integration.LocalComparisonModelIntegrable

/-! Spatial tails of the actual prescribed analytic marked packets. The
original coupling, labels, test variables, phases, and token values are
retained. Only membership in a fixed set of original rows is tested. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPrescribedPacketTail
open Function Finset Lattice Wilson RG Marker LocalComparison LocalComparison.MarkedPackets
open Push.AbsoluteSums Comparison.Density.RenderM
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] {R : Census V}
    {D : V → ComparisonDensity.Address.Orbit} (P : MarkedPackets D G n R) {p : BudgetPoint}
    {address : V → Support n} {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {g width budget : ℝ} {coverOffset coverSlope : ℕ}

private lemma kept {T : Type*} {q : Prop} {a : Option T} {b : T} (h : (if q then a else none)=some b) : a=some b := by
  by_cases hq : q
  · simpa only [if_pos hq] using h
  · simp [hq] at h

def depth (i : ℕ) := (P.packet i).elim 0 (fun T => T.fall)

def slice (keep : ℕ → Prop) : MarkedPackets D G n R :=
  { P with packet := fun i => if keep i then P.packet i else none
           marked := fun i T h => P.marked i T (kept h)
           rank_bounded := fun i T h => P.rank_bounded i T (kept h)
           power_bounded := fun i T h => P.power_bounded i T (kept h)
           nonnegative_grade := fun i T h => P.nonnegative_grade i T (kept h) }

private def halfPoint (p : BudgetPoint) : BudgetPoint :=
  {p with supportExponent := p.supportExponent/2,exponent_pos := half_pos p.exponent_pos}

/-- The authentic rooted inventory pays the clipped chamber before every field and
independent test. Half the original exponential width remains in the new bill. -/
private theorem funded (H : P.Paid p address region w g width budget coverOffset coverSlope)
    (keep : ℕ → Prop) (r : ℕ) (low : ∀ i, keep i → r ≤ depth P i) :
    (slice P keep).Paid (halfPoint p) address region w g (width/2)
      (Real.exp (-(width*(r:ℝ))/2)*budget) coverOffset coverSlope := by
  refine {
    width_pos := half_pos H.width_pos
    positive := H.positive
    coefficient := fun i T hi=>H.coefficient i T (kept hi)
    paths := fun i T hi=>H.paths i T (kept hi)
    addresses := fun i T hi=>H.addresses i T (kept hi)
    symmetry := fun i T hi=>H.symmetry i T (kept hi)
    reads := fun i T hi=>H.reads i T (kept hi)
    multilinear := fun i T hi=>H.multilinear i T (kept hi)
    roots := ?_
    cover := fun i T hi=>H.cover i T (kept hi)
    width_reserved := ?_ }
  · intro v
    apply budget_mono (budget_scale (Real.exp_pos _).le (H.roots v))
    · intro i
      by_cases hv : v∈(P.mode i).val <;> by_cases hk : keep i <;> simp only [slice,hv,hk,ite_true,ite_false,ite_self,le_refl]
      cases e : P.packet i with
      | none => simp
      | some T =>
        have hc := (H.coefficient i T e).1
        have hw := (Poly.worth H.positive (P.mode i)).le
        positivity
    · intro i
      by_cases hv : v∈(P.mode i).val
      · by_cases hk : keep i
        · simp only [slice,hv,hk,ite_true]
          cases e : P.packet i with
          | none => simp
          | some T =>
            have hf : r ≤ T.fall := by simpa [depth,e] using low i hk
            have hh := mul_le_mul_of_nonneg_left (show (r:ℝ)≤T.fall by exact_mod_cast hf) H.width_pos.le
            have he : Real.exp (width/2*T.fall) ≤ Real.exp (-(width*(r:ℝ))/2)*Real.exp (width*T.fall) := by
              rw [←Real.exp_add,Real.exp_le_exp]
              linarith
            have hc := (H.coefficient i T e).1
            have hw := (Poly.worth H.positive (P.mode i)).le
            calc _ ≤ (Poly.toll w (P.mode i)*‖(g:ℂ)^P.power i‖*T.coin)*(Real.exp (-(width*(r:ℝ))/2)*Real.exp (width*T.fall)) :=
                    mul_le_mul_of_nonneg_left he (by positivity)
                 _ = _ := by ring
        · have hsp := mul_nonneg (Real.exp_pos (-(width*(r:ℝ))/2)).le ((H.roots v).1 i)
          simpa only [slice,hv,hk,ite_true,ite_false] using hsp
      · simp [slice,hv]
  · change p.supportExponent/2*(coverSlope:ℝ)/(p.B:ℝ) ≤ (width/2)/4
    calc _ = (p.supportExponent*(coverSlope:ℝ)/(p.B:ℝ))/2 := by ring
         _ ≤ (width/4)/2 := div_le_div_of_nonneg_right H.width_reserved (by norm_num)
         _ = _ := by ring

variable [Fintype V]
/-- Every actual long signed model read has a volume-free exponentially small
full weighted price. The retained subseries is summable on the actual field. -/
theorem long_read (H : P.Paid p address region w g width budget coverOffset coverSlope)
    (r cap : ℕ) (hcap : P.rankCap ≤ cap) (x : IndependentTests D) (U : Config G n) :
    let Q := slice P (fun i => r ≤ depth P i)
    Summable (fun i => Poly.send (Q.mode i) (Q.term (testInclusion D x) g U i)) ∧
      Poly.price w (Q.read (testInclusion D x) g U) ≤ uniformReadCost cap (Fintype.card V)
        (Real.exp (-(width*(r:ℝ))/2)*budget) :=
  (funded P H _ r (fun _ h=>h)).uniform_read cap hcap x U

/-- The true selected subseries has a bounded measurable nonlinear multiplier
on each regulator, even for arbitrary source tests. -/
theorem envelope (H : P.Paid p address region w g width budget coverOffset coverSlope)
    (hsum : ∀ (x : TestSpace D) (U : Config G n), Summable (fun i => Poly.send (P.mode i) (P.term x g U i)))
    (keep : ℕ → Prop) (x : TestSpace D) :
    Envelope (fun U : Config G n => Poly.pass ((slice P keep).read x g U)) := by
  apply (funded P H keep 0 (fun _ _ => Nat.zero_le _)).multiplier_envelope _ x
  intro z U
  have hs := (hsum z U).indicator {i | keep i}
  refine hs.congr (fun i=>?_)
  by_cases h : keep i
  · cases e : P.packet i <;> simp [slice,MarkedPackets.term,h,e]
  · simp [slice,MarkedPackets.term,h]

end YM.Integration.WilsonPrescribedPacketTail
