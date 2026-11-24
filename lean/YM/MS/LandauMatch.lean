import YM.MS.MasterRight
/-! Assemble the estimates for the two chosen Domain paths (plane-wave convention).
Normalization `(2π)^-4`; cutoff is on closed zone, use restricted measure there.
`Master` asserts identities tested on bulk/anchored real nets, signs as chosen.
No assumption of physical-state transversality. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Landau
open Plane Flux Function Filter Set Koszul Wire Real MeasureTheory LogTime LogTime.IntervalFamily Momentum Domain
open scoped ContDiff Topology
variable {A C ι : Type} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
    {R : LogTime.IntervalFamily ι} {S: Scale ι} {y:ℝ}

/-! Define two masters corresponding to matched-scale kernels. For now corners only. -/
def covMeasure (A : Type) [Fintype A]: Measure (Momentum A) := ENNReal.ofReal ((2*π) ^ Fintype.card A)⁻¹ • (volume : Measure (Momentum A)) -- parses as `(ofReal ((...^)⁻¹))`?
instance measure_spec : Measure.IsAddHaarMeasure (covMeasure A):= by
   unfold covMeasure; exact Measure.IsAddHaarMeasure.smul _ (by positivity) (by finiteness) -- check

variable (A C)
def zL : Domain (parity (A:=A) (C:=C)) (Momentum A) where
   meter t := choir (line (exp t)) wave
   measure := (covMeasure A).restrict (firstZone A)

def zD : Domain (parity (A:=A) (C:=C)) (Momentum A) where
   meter t:= choir (line (exp t)) id
   measure := covMeasure A
instance rmeasure : Measure.IsAddHaarMeasure (zD A C).measure:= measure_spec
variable {A C}
omit [Fintype C] in
lemma criterion [Nonempty ι] (f: ∀ i:R.Inst, phaseDiff R.primary i ≤ rate R y i): Charge.Criteria (A:=Leg A C) R wfield y (send wave) (send id) where
   cost i j:= send_cost (S:=R.primary) (fun i=> one_le_exp (show 0≤t i from (R.beg_nn _).trans i.ge)) f i j
   shape i j:= by
      refine ⟨((send_cost (S:=R.primary) (fun u=> one_le_exp ((R.beg_nn _).trans u.ge)) f i j).std.smooth (R.start (Classical.arbitrary _))),?_,?_⟩ <;> (unfold send; dsimp only ; unfold choir; split)
      · intro he; rcases i with ⟨⟨k,_|_⟩,s⟩ <;> rcases j with ⟨⟨l,_|_⟩,u⟩ <;> norm_num [wfield,dim] at he
      · exact fun _=> rfl
      · intro z x; rcases i with ⟨⟨_|k,_|_⟩,s⟩ <;> rcases j with ⟨⟨_|l,_|_⟩,u⟩ <;> norm_num [bare,wfield,dim,Complex.real_smul,k_scale, zpow_natCast] <;> ring_nf; exact Or.inl rfl
      simp
lemma primary_large (h : y ≤1) (u:R.Inst) : phaseDiff R.primary u ≤ rate R y u := by
   unfold phaseDiff rate; change (exp (t u)^2)⁻¹ ≤ _; rw [← exp_nat_mul, ← exp_neg, exp_le_exp]; have hv := (R.beg_nn _).trans u.ge; norm_num; nlinarith

variable {h : ℤ} {b : Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {w : Wire (Leg A C) E (Momentum A)}
    {G F L Q : Target (Leg A C) (Momentum A) (Clock ι)}

lemma land_value (hi : y≤1) (hm : Fintype.card A=4) (n d : ℕ) (c : ℂ)
    (hw : Course b w) (HO : Match R.primary b (lane R (F n)) (lane R (Q n)) h (rate R y) wfield (w.length+2))
    (FG : ∀ i∈paths n d, ∀ r, Match R.primary true (lane R (G (n-i))) (lane R (L (n-i))) 4 (rate R y) wfield (r+1))
    (H : ∀ i∈paths n d, ∀ r, Match R.primary b (lane R (F i)) (lane R (Q i)) h (rate R y) wfield (r+1)) : Light R.primary (rate R y) wfield (lane R ((zL A C).recu d c G F n)) (lane R ((zD A C).recu d c L Q n)) w h := by
   convert! recu_cost R (zL A C) (zD A C) (firstZone A) rfl (measurableSet_closedBall) zone' 2 (primary_large hi) (by simpa using hm) (line_meter (fun i:R.Inst=> Real.one_le_exp ((R.beg_nn _).trans i.ge)) (primary_large hi)) n d c hw HO FG H using 1; omega

end YM.MS.Landau
