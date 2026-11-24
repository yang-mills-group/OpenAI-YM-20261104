import YM.Pert.Deeper

/-!
# Step spacing budget. Not yet buying all the demands of E1 or (gramdelay)!

We do fix from the start the power-of-3 ratio convention and buy
- L <= log Lambda (Lambda = 2 + log hatted beta, NOT monitor), and
  an optional stage-only fee; for all m, even across stages;
- the Plenty budget for kinetic and spatial costs in Pert.

All on one schedule. Enlarge upon any other demands which fit this
dependency order (not asserting others do). One stagewise fee programme may
include finitely many neighbours, and can set up growing finite demands -- it
may not read off actual pace/beta/volumes not yet available, nor be used to
retune separately for each output order. Adapt Rolls/halo_delay and Pert.Deeper.
-/

noncomputable section
set_option autoImplicit false
namespace YM.RG16
open Function Set Filter Lattice Wilson Precision RG RG.Supply MergeProof Push.PriceCompiler
open scoped Topology BigOperators
variable {G:Gauge}

def Lambda (a:Levels G) (m:ℕ) := 2+Real.log (a.clock.hatBeta m)

def Threes {s : Sheet G} (D : Rolls s) : Prop := ∀ j, ∃ k:ℕ,(D.L j).val=3^k

lemma buy_threes (p : Sheet G) (h : G.Simple) : ∃ D:Rolls p, Threes D := by
  choose C H using fun i => Rolls.eventually_large p h i
  let M := fun i => (Finset.range (i+1)).sup C
  have hm : Monotone M := fun i j hij => Finset.sup_mono (Finset.range_mono (by omega))
  let L(i:ℕ) := (⟨3^(M i), by positivity⟩:Side)
  refine ⟨⟨L,fun i => H i _ ?_ ?_,fun i j hij => pow_le_pow_right₀ ?_ (hm hij)⟩,
     fun i => ⟨_,rfl⟩⟩
  · apply le_trans (show C i ≤ M i from Finset.le_sup (Finset.mem_range.mpr (by omega)))
    suffices h : ∀ n:ℕ,n < 3^n from (h _).le
    intro n; induction n with
    | zero => simp
    | succ n ih => rw [pow_succ]; omega
  · exact (show Odd (3:ℕ) from ⟨1,rfl⟩).pow
  norm_num

def PlentyGate (a : Levels G) : Prop :=
    ∀ i, ((a.budget i).supportExponent+1)*(((a.S.block (i-1)).val:ℕ):ℝ)^4 ≤
      Real.sqrt (a.clock.hatBeta i)
lemma plenty_of (C:Family G) (h:PlentyGate C.path.levels) : Ribbons.Plenty C := h
section
variable {s : Sheet G} (D: Rolls s) {T:Protection D}
-- Pretty painful price of using a future analyst's proof in this location is
-- checking its arguments: only the realized stage fee, already fixed here.
lemma later (hG:G.Simple) (V : Delays T) (postFee:ℕ → ℝ) :
    ∃ W, DelayLe V W ∧ ∀ W', DelayLe W W' →
     ∀ {X : Bar W'} (P : Wait X) (A : Levels G), Paid P A →
       PlentyGate A ∧ ∀ m,
         max ((A.S.block m).val:ℝ) (postFee (A.clock.J (m+1))) ≤ Real.log (Lambda A m) := by
  let F (j:ℕ) (x:ℝ) : Prop := ((((s.profile j).supportExponent+2)*((D.L j).val:ℝ)^4)^2 ≤ x) ∧
       max ((D.L j).val:ℝ) (postFee j) ≤ Real.log (2+Real.log x)
  have h (j:ℕ) : ∀ᶠ x in atTop, F j x :=
    (eventually_ge_atTop _).and ((Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_left _ (2:ℝ) Real.tendsto_log_atTop)).eventually_ge_atTop _)
  obtain ⟨W,hW,-,h'⟩ := delay_extra V F (fun _ _ _ => True) h (fun _ _=>by simp)
  refine ⟨W,hW,fun W' hW' _ P A hA =>?_⟩
  have hb(m:ℕ) := (h' W' hW').1 (A.clock.J (m+1)) _ (hA.pays m)
  refine ⟨?_,fun m=>?_⟩
  · -- adapt standalone price from Pert/Dense/Kernel
    intro i
    rw [Push.PriceCompiler.block_eq hA]
    let j := A.clock.J ((i-1)+1)
    have he : A.clock.J i = j := by
       cases i with
       | zero => dsimp only [j]; rw [hA.firstZero, show 0-1+1=1 by norm_num, hA.firstOne]
       | succ i => rfl
    have hl : (A.budget i).supportExponent= (s.profile j).supportExponent := by
       change (A.clock.stage (A.clock.J i)).supportExponent=_; rw [he,hA.stage]
    have hpay : A.clock.hatBeta (i-1) ≤ A.clock.hatBeta i := by
       unfold YM.RG.Calendar.hatBeta; gcongr
       · exact (Gauge.slopeConstant_pos hG).le
       cases i with
       | zero=>rfl
       | succ i =>
         change A.S.scale i ≤ A.S.scale (i+1); rw [A.S.scale_succ]; exact (by linarith [Real.log_nonneg (Nat.one_le_cast.mpr (A.S.block i).pos)])
    have hLow : (((s.profile j).supportExponent+2)*((D.L j).val:ℝ)^4)^2 ≤ A.clock.hatBeta i :=
      (hb (i-1)).1.trans hpay
    have hh : ((s.profile j).supportExponent+2)*((D.L j).val:ℝ)^4 ≤ Real.sqrt (A.clock.hatBeta i) := by
      nlinarith only [hLow,Real.sq_sqrt (zero_lt_one.trans (A.fits.delayed i)).le,Real.sqrt_nonneg (A.clock.hatBeta i)]
    apply le_trans _ hh; rw [hl]; gcongr; linarith
  rw [Push.PriceCompiler.block_eq hA]; exact (hb m).2
end
end YM.RG16
