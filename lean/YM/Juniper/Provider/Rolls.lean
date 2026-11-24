import YM.Juniper.Provider.Column
import YM.Pert.Dense.Kernel
import YM.OPE.Rough.Gate
/-! Reserve for the joins, including qpta powers-of-three and
   slow z-cost for several often used quantities. Further width/field/etc.
   reserves are not implied. Future consumers can insert both additional
   pre-L costs (`juniper_wishes` followed by `rolls`) and user-defined delays
   BEFORE selecting the actual witness. -/
set_option autoImplicit false
noncomputable section
namespace YM.Juniper
open Function Filter Lattice RG Wilson Pressure RG.Supply Push.PriceCompiler
open Extra.Histories Labels MergeProof Bid Motion
open scoped Topology BigOperators Classical
variable {G : Gauge} {S : Sheet G} {D : Rolls S} {T : Protection D}

def PowerRolls (D : Rolls S) := ∀ i, ∃ e : ℕ, (D.L i).val = 3^e

lemma rolls (hG : G.Simple) (S : Sheet G) (N : ℕ → ℕ) :
    ∃ D : Rolls S, ColumnPre S D ∧ PowerRolls D ∧ N ≤ fun i => (D.L i).val := by
  choose C H using fun i => Rolls.eventually_large S hG i
  choose q hq using fun i d => Doors.pre_tilt (2 * (S.profile i).columns) (orbitCost ((frames G).level d))
  let a i := (Finset.range (i+1)).sup (q i)
  let M (i) := (Finset.range (i+1)).sup fun j => max (a j) (max (C j) (N j))
  let P := fun i => (⟨3^(M i), by positivity⟩:Side)
  have hm : Monotone M := fun _ _ hij => Finset.sup_mono (Finset.range_mono (by omega))
  have hc (i) : max (a i) (max (C i) (N i)) ≤ (P i).val := by
    refine (Finset.le_sup (s:=Finset.range (i+1)) (f:=fun j=>max (a j) (max (C j) (N j))) (by simp : i ∈ _)).trans
      (?_ : M i ≤ 3^M i)
    generalize M i = n
    exact le_trans (Nat.lt_two_pow_self.le) (pow_le_pow_left' (by norm_num : (2:ℕ) ≤ 3) n)
  refine ⟨⟨P,fun j=> H j _ ((le_max_left ..).trans ((le_max_right ..).trans (hc j))) (by exact (show Odd (3:ℕ) from ⟨1,rfl⟩).pow), fun i j hij=> pow_le_pow_right' (by norm_num : (1:ℕ)≤3) (hm hij)⟩,
    fun j d hd=>?_, fun i=>⟨_,rfl⟩, fun i=> (le_max_right ..).trans ((le_max_right ..).trans (hc i))⟩
  let L := P j; intro u
  have hh := (hq j d (P j) (le_trans (b:= a j)
    (Finset.le_sup (by exact Finset.mem_range.mpr (Nat.lt_succ_of_le hd))) ((le_max_left ..).trans (hc j)))).2
  convert hh using 1
  change (Doors.rate L + 2 * Doors.rate L * _) * _ = Doors.rate L * (1 + 2 * _) * _; ring

def Lambda (s : Levels G) (i : ℕ) : ℝ := 2 + Real.log (s.clock.hatBeta i)
def zcost (s : Levels G) (i : ℕ) : ℝ := 1 + Real.log (Real.log (s.clock.hatBeta i))
def joinSize (L : Side) (v : Stage) : ℝ := 1 + L.val + v.order + v.power +
  v.columns + v.supportExponent + v.width⁻¹ + v.paths + |v.clip.relaxation|
def Slow (s : Levels G) := ∀ i : ℕ, joinSize (s.S.block i) (s.params (i+1)) ≤ zcost s i

def deepBill (S : Sheet G) (D : Rolls S) (i : ℕ) :=
  (((S.profile i).supportExponent + 2)*((D.L i).val:ℝ)^4)^2

lemma join_delay (V : Delays T) : ∃ W, DelayLe V W ∧ ∀ V', DelayLe W V' →
    deepBill S D ≤ V'.betaEntry ∧ ∀ {Z : Bar V'} (P : Wait Z) (s : Levels G),
        Paid P s → OPE.HaloGate s ∧ Slow s := by
  let V₀ : Delays T := { V with betaEntry := fun i => max (V.betaEntry i) (deepBill S D i) }
  have hV₀ : DelayLe V V₀ := ⟨fun _=> le_max_left .., le_rfl, le_rfl, le_rfl⟩
  obtain ⟨V₁,h₁,hH⟩ := OPE.halo_delay V₀
  have hs (i : ℕ) : ∀ᶠ x : ℝ in atTop,
      joinSize (D.L i) (S.profile i) ≤ 1+Real.log (Real.log x) := by
    filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop
        (joinSize (D.L i) (S.profile i))] with x hx
    exact hx.trans (le_add_of_nonneg_left zero_le_one)
  obtain ⟨W,hW,-,h⟩ := delay_extra V₁ _ (fun _ _ _ => True) hs (fun _ _ => by simp)
  refine ⟨W,hV₀.trans (h₁.trans hW),fun U hu=> ⟨(show deepBill S D ≤ V₀.betaEntry from fun i=> le_max_right ..).trans ((h₁.trans (hW.trans hu)).beta),fun P s hS=> ⟨hH U (hW.trans hu) P s hS,fun i=>?_⟩⟩⟩
  have ho := (h U hu).1 _ _ (hS.pays i)
  rw [Extra.Iteration.block_eq hS, params_eq hS]
  exact ho

/-- The spending of the post-L delay follows `Pert.Dense.deeperBinding`.
  Plenty is deliberately stated on (i-1); include the floor/first plateau. -/
lemma plenty (C : Family G) {I : Delays T} {B : Bar I} {X : Wait B}
    (hG : G.Simple) (h : Paid X C.path.levels) (hI : deepBill S D ≤ I.betaEntry) :
    Ribbons.Plenty C := by
  let a := C.path.levels
  unfold Ribbons.Plenty Ribbons.spacingFactor; intro i
  rw [show a.S=a.clock.schedule from rfl,← a.fits.sameFactor (i-1)]
  let j:=a.clock.J ((i-1)+1)
  have h0 : i = (i-1)+1 ∨ a.clock.J i = a.clock.J ((i-1)+1) := by
    cases i with
    | zero => right; unfold a; rw [h.firstZero, show 0-1+1=1 by norm_num, h.firstOne]
    | succ i => exact Or.inl rfl
  have hj : a.clock.J i = j := by rcases h0 with h|h; exact congr_arg _ h; exact h
  have he : ((a.budget i).supportExponent)= (S.profile j).supportExponent := by
    change (a.clock.stage (a.clock.J i)).supportExponent=_; rw [hj]; unfold a; rw [h.stage]
  have hhat : a.clock.hatBeta (i-1) ≤ a.clock.hatBeta i := by
    unfold YM.RG.Calendar.hatBeta; gcongr
    · exact (Gauge.slopeConstant_pos hG).le
    cases i with
    | zero => rfl
    | succ i =>
      change a.S.scale i ≤ a.S.scale (i+1); rw [a.S.scale_succ]; exact (by linarith [Real.log_nonneg (Nat.one_le_cast.mpr (a.S.block i).pos)])
  have hLow : (((S.profile j).supportExponent+2)*((D.L j).val:ℝ)^4)^2 ≤ a.clock.hatBeta i :=
    (hI j).trans ((h.pays (i-1)).trans hhat)
  have hh : ((S.profile j).supportExponent+2)*((D.L j).val:ℝ)^4 ≤ Real.sqrt (a.clock.hatBeta i) := by
    nlinarith only [hLow,Real.sq_sqrt (zero_lt_one.trans (a.fits.delayed i)).le,Real.sqrt_nonneg (a.clock.hatBeta i)]
  change ((a.budget i).supportExponent+1)*(a.clock.factor j |>.val:ℝ)^4 ≤ _
  refine le_trans ?_ hh; rw [he,show a.clock.factor = _ from h.lengths]; gcongr; linarith

end YM.Juniper
