import YM.Integration.WilsonGraphIssuedOrdinaryGraphBasis
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedFieldDegreeAllocations

noncomputable section
namespace YM.Integration.AppointedOrdinaryFiledInputs
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
open YangMills YangMills.Matching
open YM.XSpace YM.XSpace.Normalize YM.FVA2 YM.FVA2.Dframe
open YM.FVA2.O YM.FVA2.O.Score YM.FVA2.O.Project YM.FVA2.O.Canon
open YM.FVA2.Scale YM.Answer.ContinuumLimit PowerSeries
open _root_.IssuedMaxwell _root_.IssuedMaxwell.Reports
open scoped BigOperators Classical

/-- Collect all incoming heater degrees and substitute the filed scalar in the remaining coefficient. -/
theorem degrees {n : ℕ} (a : Fin n → PowerSeries ℂ) (c p : PowerSeries ℂ)
    (f : ℕ → ℝ) (hc : ∀ i, coeff i c = (f i : ℂ)) (hf : f 0 = 0) (k : ℕ) :
    coeff k ((∏ i, a i) * p.subst c) =
      ∑ ν : Fin n → Fin (k+1), ∑ j : Fin (k+1),
        if (∑ i, (ν i).val) ≤ k then
          (couplingPower f j.val (k-∑ i, (ν i).val) : ℂ) *
            (∏ i, coeff (ν i).val (a i)) * coeff j.val p
        else 0 := by
  rw [Dframe.Constants.admits]
  have collected := _root_.IssuedBridge.PostedFieldDegreeAllocations.original (n:=n) (k:=k)
    (fun l e => (∏ i, coeff (e i) (a i)) * coeff l (p.subst c))
  refine collected.trans (Finset.sum_congr rfl fun ν _ => ?_)
  by_cases inCrop : (∑ i, (ν i).val) ≤ k
  · simp only [inCrop, if_true]
    rw [AppointedNullaryRefund.substituted c p f hc hf _ k (Nat.sub_le _ _), Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  · simp [inCrop]

/-- The extra series is the actual outgoing cap-h field factor, charged inside the same total degree. -/
theorem withOutput {n : ℕ} (a : Fin n → PowerSeries ℂ) (o c p : PowerSeries ℂ)
    (f : ℕ → ℝ) (hc : ∀ i, coeff i c = (f i : ℂ)) (hf : f 0 = 0) (k : ℕ) :
    coeff k (((∏ i, a i) * p.subst c) * o) =
      ∑ ν : Fin n → Fin (k+1), ∑ j : Fin (k+1), ∑ b : Fin (k+1),
        if b.val + (∑ i, (ν i).val) ≤ k then
          (couplingPower f j.val (k-(b.val + ∑ i, (ν i).val)) : ℂ) *
            (coeff b.val o * ∏ i, coeff (ν i).val (a i)) * coeff j.val p
        else 0 := by
  let A : Fin (n+1) → PowerSeries ℂ := Fin.cons o a
  have product : (∏ i, A i) = o * ∏ i, a i := Fin.prod_univ_succ A
  have arranged : ((∏ i, a i) * p.subst c) * o = (∏ i, A i) * p.subst c := by
    rw [product]
    ring
  rw [arranged, degrees A c p f hc hf k]
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Fin (k+1))), Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.consEquiv, Equiv.coe_fn_mk,
    Fin.cons_zero, Fin.cons_succ, A]

variable (g : YangMills.GaugeGroup) {n : ℕ}

/-- Apply each native heater column to an occupied homogeneous basis input at its actual cap. -/
theorem basisColumns (F : Scale.Frames g.core) (H : Civil F) (d : Fin n → ℕ)
    (s : (i : Fin n) → Toon g.core (d i)) (e : Fin n → ℕ) (h j : ℕ) (x : YM.Points n) :
    GraphReader.form g d h j x (fun i => coeff (e i) (F (d i)) (theory (s i))) =
      ∑ w : LivesP (fun i => Dframe.flash (s i)),
        (∏ i, coeff (e i) (cue (seats F) (Dframe.flash (s i)) (own (w i)))) •
          GraphReader.earned g (fun i => own (w i)) h j x := by
  let B : MultilinearMap ℂ (fun i => Sec g.core (d i)) (Sec g.core h) := GraphReader.form g d h j x
  let col (i : Fin n) (b : Grade g.core (s i).1.val) :=
    coeff (e i) (cue (seats F) (Dframe.flash (s i)) (own b))
  have atSlot (i : Fin n) : coeff (e i) (F (d i)) (theory (s i)) =
      ∑ b : Grade g.core (s i).1.val, col i b • theory (⟨(s i).1,b⟩ : Toon g.core (d i)) :=
    cap_map H (Dframe.flash (s i)) (Nat.le_of_lt_succ (s i).1.isLt) (e i)
  calc
    _ = B (fun i => ∑ b : Grade g.core (s i).1.val, col i b •
        theory (⟨(s i).1,b⟩ : Toon g.core (d i))) := congrArg B (funext atSlot)
    _ = ∑ w : (i : Fin n) → Grade g.core (s i).1.val,
        B (fun i => col i (w i) • theory (⟨(s i).1,w i⟩ : Toon g.core (d i))) := B.map_sum _
    _ = _ := by
      refine Finset.sum_congr rfl fun w _ => ?_
      exact (B.map_smul_univ (fun i => col i (w i))
        (fun i => theory (⟨(s i).1,w i⟩ : Toon g.core (d i)))).trans
        (congrArg _ (GraphReader.marked g d (fun i => ⟨(s i).1,w i⟩) h j x))

/-- Expand the actual inhomogeneous input once, before applying its heater-dependent columns. -/
theorem inputColumns (F : Scale.Frames g.core) (H : Civil F) (d : Fin n → ℕ)
    (v : (i : Fin n) → Sec g.core (d i)) (e : Fin n → ℕ) (h j : ℕ) (x : YM.Points n) :
    GraphReader.form g d h j x (fun i => coeff (e i) (F (d i)) (v i)) =
      ∑ s : (i : Fin n) → Toon g.core (d i), (∏ i, coord (s i) (v i)) •
        ∑ w : LivesP (fun i => Dframe.flash (s i)),
          (∏ i, coeff (e i) (cue (seats F) (Dframe.flash (s i)) (own (w i)))) •
            GraphReader.earned g (fun i => own (w i)) h j x := by
  let B : MultilinearMap ℂ (fun i => Sec g.core (d i)) (Sec g.core h) := GraphReader.form g d h j x
  have each (i : Fin n) : coeff (e i) (F (d i)) (v i) =
      ∑ s : Toon g.core (d i), coord s (v i) • coeff (e i) (F (d i)) (theory s) := by
    have expansion : v i = ∑ s : Toon g.core (d i), coord s (v i) • theory s := (all_sig (v i)).symm
    calc
      _ = coeff (e i) (F (d i)) (∑ s : Toon g.core (d i), coord s (v i) • theory s) :=
        congrArg _ expansion
      _ = _ := by rw [map_sum]; simp only [map_smul]
  calc
    _ = B (fun i => ∑ s : Toon g.core (d i), coord s (v i) •
        coeff (e i) (F (d i)) (theory s)) := congrArg B (funext each)
    _ = ∑ s : (i : Fin n) → Toon g.core (d i), B (fun i => coord (s i) (v i) •
        coeff (e i) (F (d i)) (theory (s i))) := B.map_sum _
    _ = _ := by
      refine Finset.sum_congr rfl fun s _ => ?_
      exact (B.map_smul_univ (fun i => coord (s i) (v i))
        (fun i => coeff (e i) (F (d i)) (theory (s i)))).trans
        (congrArg _ (basisColumns g F H d s e h j x))

end YM.Integration.AppointedOrdinaryFiledInputs

