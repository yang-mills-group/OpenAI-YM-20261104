import YM.Integration.OriginalRootedPacketLayout
import Mathlib.Logic.Denumerable

/-! The selected rooted measure gives one literal marked packet bank,
including the full nonlinear curvature completions. Its unweighted invoice
is obtained on these same coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalFundedMarkedPackets
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Marker Precision Tree Laurent
open ComparisonDensity.Address Comparison.Density.RenderM LocalComparison
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Soil
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider
open WilsonCoeffUV.Embroider.Canvas FundedMarkedPathSelection OriginalRootedPacketLayout Work.F08
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel.Flooring
open scoped BigOperators Classical Topology ContDiff

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
variable (C : Census V) (k : V → ℕ) {e : ℕ} {n : Side} (p : V → Site n)
variable (O : V → Orbit) (Y : V → Dip) {m N : ℕ}
variable (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) {A : ℝ}
variable (X : Input Q hm Finset.univ k (NativeMarkedAddressTokens.axes O) A)
local notation "St" => Block C k e
local notation "Rows" => Row (G:=G) C k e
variable (μ : MeasureArray C k O (e:=e) (G:=G))

def layout : ℕ ≃ (Rows ⊕ ℕ) := Classical.choice inferInstance

private def rankAt : (Rows ⊕ ℕ) → ℕ := Sum.elim (fun a => a.1.2.2.val) (fun _ => 0)

private def atRow (a : Rows ⊕ ℕ) :
    Option (Token G n (fun i => (O i).Mood) (rankAt C k (e:=e) (G:=G) a)) :=
  match a with
  | .inl v => some (token C k p O Y Q hm X (N:=N) μ v)
  | .inr _ => none

private theorem liveFacts (a : Rows ⊕ ℕ)
    (t : Token G n (fun v => (O v).Mood) (rankAt C k (e:=e) (G:=G) a))
    (ht : atRow C k p O Y Q hm X (N:=N) μ a = some t) :
    Sum.elim (fun b : Rows => b.1.1.val) (fun _ => C.quiet) a ≠ C.quiet ∧
    rankAt C k (e:=e) (G:=G) a ≤ cap k e ∧
    (Sum.elim (fun b : Rows => power C k e b.1) (fun _ => 0) a).natAbs ≤ cap k e ∧
    0 ≤ Sum.elim (fun b : Rows => power C k e b.1) (fun _ => 0) a +
      (rankAt C k (e:=e) (G:=G) a : ℤ) := by
  cases a with
  | inr a => cases ht
  | inl a =>
    refine ⟨?_,degree_le C k e a.1,power_le C k e a.1,?_⟩
    · change a.1.1.val ≠ C.quiet
      intro h
      have active : a.1.1.val.val.Nonempty := a.1.1.property
      rw [h] at active
      exact Finset.not_nonempty_empty active
    · change 0 ≤ ((a.1.2.1.val : ℤ) - a.1.2.2.val) + a.1.2.2.val
      omega

def packets : MarkedPackets O G n C where
  mode i := Sum.elim (fun v : Rows => v.1.1.val) (fun _ => C.quiet) (layout C k (G:=G) (e:=e) i)
  rank i := rankAt C k (e:=e) (G:=G) (layout C k (G:=G) (e:=e) i)
  power i := Sum.elim (fun v : Rows => power C k e v.1) (fun _ => 0) (layout C k (G:=G) (e:=e) i)
  packet i := atRow C k p O Y Q hm X (N:=N) μ (layout C k (G:=G) (e:=e) i)
  marked i t h := (liveFacts C k p O Y Q hm X (N:=N) μ (layout C k (G:=G) (e:=e) i) t h).1
  rankCap := cap k e
  powerCap := cap k e
  rank_bounded i t h := (liveFacts C k p O Y Q hm X (N:=N) μ (layout C k (G:=G) (e:=e) i) t h).2.1
  power_bounded i t h := (liveFacts C k p O Y Q hm X (N:=N) μ (layout C k (G:=G) (e:=e) i) t h).2.2.1
  nonnegative_grade i t h := (liveFacts C k p O Y Q hm X (N:=N) μ (layout C k (G:=G) (e:=e) i) t h).2.2.2


private theorem present
    (law : (s : C.Mode) → (r : ℕ) → Token G n (fun i => (O i).Mood) r → Prop)
    (physical : ∀ a : Rows, law a.1.1.val a.1.2.2.val (token C k p O Y Q hm X (N:=N) μ a))
    (i : ℕ) : ∀ t, (packets C k p O Y Q hm X (N:=N) μ).packet i = some t → law ((packets C k p O Y Q hm X (N:=N) μ).mode i) ((packets C k p O Y Q hm X (N:=N) μ).rank i) t := by
  change ∀ t, atRow C k p O Y Q hm X (N:=N) μ (layout C k (G:=G) (e:=e) i) = some t →
    law (Sum.elim (fun a : Rows => a.1.1.val) (fun _ => C.quiet) (layout C k (G:=G) (e:=e) i))
      (rankAt C k (e:=e) (G:=G) (layout C k (G:=G) (e:=e) i)) t
  generalize layout C k (G:=G) (e:=e) i = z
  cases z with
  | inr _ => intro t h; cases h
  | inl a => intro t h; cases h; exact physical a

/-- This signed integer is stored in the same row which carries the
corresponding complete unmasked field and all independent source kernels. -/
theorem graded (a : Rows) :
    let i := (layout C k (G:=G) (e:=e)).symm (.inl a)
    (packets C k p O Y Q hm X (N:=N) μ).mode i = a.1.1.val ∧ (packets C k p O Y Q hm X (N:=N) μ).power i = (a.1.2.1.val:ℤ)-(a.1.2.2.val:ℤ) ∧
      (packets C k p O Y Q hm X (N:=N) μ).rank i = a.1.2.2.val ∧ ∀ x g U,
      (packets C k p O Y Q hm X (N:=N) μ).term x g U i = (g : ℂ)^((a.1.2.1.val:ℤ)-(a.1.2.2.val:ℤ)) *
        (token C k p O Y Q hm X (N:=N) μ a).read x U := by
  refine ⟨by simp [packets],by simp [packets,power],by simp [packets,rankAt],?_⟩
  intro x g U
  let value (z : Rows ⊕ ℕ) : ℂ :=
    match atRow C k p O Y Q hm X (N:=N) μ z with
    | none => 0
    | some t => (g:ℂ) ^ Sum.elim (fun u : Rows => power C k e u.1) (fun _ => 0) z * t.read x U
  have readAt (i : ℕ) : (packets C k p O Y Q hm X (N:=N) μ).term x g U i =
      value (layout C k (G:=G) (e:=e) i) := by
    dsimp only [MarkedPackets.term,packets,value]
    cases h : atRow C k p O Y Q hm X (N:=N) μ (layout C k (G:=G) (e:=e) i) <;> rfl
  calc
    _ = value ((layout C k (G:=G) (e:=e)) ((layout C k (G:=G) (e:=e)).symm (.inl a))) := readAt _
    _ = value (.inl a) := congrArg value ((layout C k (G:=G) (e:=e)).apply_symm_apply (.inl a))
    _ = _ := rfl

def budget (w : V→ℝ) (g : ℝ) :=
  ∑ b : St, Poly.toll w b.1.val * ‖(g:ℂ)^(power C k e b)‖ *
    expenses C k O Q hm (A:=A) b

def offset := 1+2*cap k e + 6*Fintype.card V

private theorem packed {I : Type} {f : I → ℝ} {s : ℝ} (h : SumBudget f s) :
    SumBudget (Sum.elim f (fun _ : ℕ => 0)) s := by
  let F := Sum.elim f (fun _ : ℕ => 0)
  have he : HasSum F ((∑' i,f i)+0) :=
    HasSum.sum (f:=F) h.2.1.hasSum (hasSum_zero (β:=ℕ))
  refine ⟨fun i => by cases i with | inl a => exact h.1 a | inr _ => exact le_rfl,he.summable,?_⟩
  rw [he.tsum_eq,add_zero]
  exact h.2.2

private theorem branches {I : Type} [Fintype I] {Z : I → Type} (f : (Σ i,Z i) → ℝ)
    {c : I → ℝ} (h : ∀ i, SumBudget (fun a => f ⟨i,a⟩) (c i)) : SumBudget f (∑ i,c i) := by
  have np (a : Σ i, Z i) := (h a.1).1 a.2
  have sm := (summable_sigma_of_nonneg np).mpr ⟨fun i => (h i).2.1,(hasSum_fintype _).summable⟩
  exact ⟨np,sm,by rw [sm.tsum_sigma,tsum_fintype]; exact sum_le_sum fun i _ => (h i).2.2⟩

private theorem restrictWidth {I : Type} {f h : I → ℝ} {a b A : ℝ} (hf : ∀ i,0≤f i)
    (hh : ∀ i,0≤h i) (ab : a≤b) (orig : SumBudget (fun i => f i*Real.exp (b*h i)) A) :
    SumBudget (fun i => f i*Real.exp (a*h i)) A := by
  have np (i : I) := mul_nonneg (hf i) (Real.exp_pos (a*h i)).le
  have lt (i : I) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right ab (hh i))) (hf i)
  have sm := orig.2.1.of_nonneg_of_le np lt
  exact ⟨np,sm,(sm.tsum_le_tsum lt orig.2.1).trans orig.2.2⟩

theorem paidAt (fits : ∀ i, (Y i).Fits (O i).field)
    (raw : ∀ b t, Barn (original C k p O Q hm X (N:=N) b t) (μ b t))
    (hrow : ∀ b : St, SumBudget (fun v : RadP G b.2.2.val × Stationary.Ink G b.2.2.val =>
      let P := token C k p O Y Q hm X (N:=N) μ ⟨b,v⟩
      P.coin * Real.exp (width k Q hm * P.fall)) (expenses C k O Q hm (A:=A) b))
    (point : BudgetPoint) (w : V→ℝ) (hw : ∀ v,0<w v) (g s : ℝ) (hs : 0<s)
    (hs' : s≤width k Q hm) (space : point.supportExponent / point.B ≤ s/4) :
    (packets C k p O Y Q hm X (N:=N) μ).Paid point (fun v => {p v}) (OriginalMeasuredSourceRows.region O Y (fun v => {p v}))
      w g s (budget C k O Q hm (A:=A) w g) (offset k (e:=e)) 1 := by
  let ℓ := layout C k (G:=G) (e:=e)
  let T := token C k p O Y Q hm X (N:=N) μ
  have nonnegative (v : Rows) : 0 ≤ (T v).coin := by
    change 0 ≤ (sprigB _ _).magnitude * (NativeMarkedAddressTokens.cellPrice _ _ * _)
    exact mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (mul_nonneg (by unfold NativeMarkedAddressTokens.cellPrice; positivity) ENNReal.toReal_nonneg)
  have address (a : Rows) {v : V} (hv : v ∈ a.1.1.val.val) : {p v} ⊆ (T a).plot :=
    (Finset.subset_biUnion_of_mem (fun v => {p v}) hv).trans Finset.subset_union_right
  refine ⟨hs,hw,?_,?_,?_,?_,?_,?_,?_,?_,by simpa using space⟩
  · apply present C k p O Y Q hm X μ
      (fun _ _ t => 0≤t.coin ∧ ∀ x : IndependentTests O, (∑ j,‖t.gem j (testInclusion O x)‖) ≤ t.coin)
    exact fun v => ⟨nonnegative v,fun x =>
      (NativeMarkedAddressTokens.funds O _ Y fits _ _ (raw _ _) _ _ _ _ _ x).2⟩
  · apply present C k p O Y Q hm X μ
      (fun _ _ t => ∀ x, (t.re x).length ≤ t.fall ∧ (t.re x).footprint t.root ⊆ t.plot)
    intro a x
    let T := token C k p O Y Q hm X (N:=N) μ a
    have full : (T.re x).length ≤ T.fall ∧ (T.re x).footprint T.root ⊆ T.plot ∧
        ∀ v ∈ a.1.1.val.val, {p v} ⊆ T.plot :=
      NativeMarkedAddressTokens.supports O _ Y _ _ _ _ _ _ _ x
    exact ⟨full.1,full.2.1⟩
  · apply present C k p O Y Q hm X μ (fun s _ t => ∀ v∈s.val,{p v} ⊆ t.plot)
    exact fun v _ hv => address v hv
  · apply present C k p O Y Q hm X μ
      (fun _ _ t => ∀ x u b,t.touch x (fun i => G.adjoint b (u i)) = t.touch x u)
    exact fun _ => OriginalMeasuredSourceRows.symmetry O Y _ _ _ _ _ _ _ _
  · apply present C k p O Y Q hm X μ (fun s _ t => ∀ j,
      Comparison.Density.Testing.Reads (OriginalMeasuredSourceRows.region O Y (fun v => {p v})) t.plot s.val (t.gem j))
    exact fun _ => OriginalMeasuredSourceRows.reads O Y _ _ _ _ _ _ _ _
  · apply present C k p O Y Q hm X μ
      (fun s _ t => ∀ j, RG3.Held.Letter ℂ (fun i => (O i).Mood) s.val (t.gem j))
    exact fun _ => OriginalMeasuredSourceRows.linear O Y fits _ _ _ _ _ _ _ _ (raw _ _)
  · intro v
    let fee (a : Rows) := if v∈a.1.1.val.val then
      Poly.toll w a.1.1.val * ‖(g:ℂ)^(power C k e a.1)‖ * (T a).coin *
        Real.exp (s*(T a).fall) else 0
    have scaled (b : St) : SumBudget (fun a => fee ⟨b,a⟩)
        (Poly.toll w b.1.val * ‖(g:ℂ)^(power C k e b)‖ * expenses C k O Q hm (A:=A) b) := by
      have pos : 0 ≤ Poly.toll w b.1.val * ‖(g:ℂ)^(power C k e b)‖ :=
        mul_nonneg (Finset.prod_nonneg (fun i _ => (hw i).le)) (norm_nonneg _)
      have sel := restrictWidth (fun a => nonnegative ⟨b,a⟩) (fun _ => Nat.cast_nonneg _)
        hs' (hrow b)
      by_cases hv : v∈b.1.val.val
      · simpa [fee,hv,mul_assoc] using cap_scale sel pos
      · simp only [fee,hv,if_false]
        exact ⟨fun _ => le_rfl,summable_zero,by simpa using mul_nonneg pos (cap_nn sel)⟩
    have all := packed (branches fee scaled)
    have natural : SumBudget (fun i => Sum.elim fee (fun _ : ℕ => 0) (ℓ i))
        (budget C k O Q hm (A:=A) w g) :=
      ⟨fun i => all.1 _,ℓ.summable_iff.mpr all.2.1,by rw [ℓ.tsum_eq]; exact all.2.2⟩
    convert natural using 1
    funext i
    let settled (z : Rows ⊕ ℕ) : ℝ :=
      let mode := Sum.elim (fun a : Rows => a.1.1.val) (fun _ => C.quiet) z
      let power₀ := Sum.elim (fun a : Rows => power C k e a.1) (fun _ => 0) z
      if v ∈ mode.val then
        match atRow C k p O Y Q hm X (N:=N) μ z with
        | none => 0
        | some t => Poly.toll w mode * ‖(g:ℂ)^power₀‖ * t.coin * Real.exp (s*t.fall)
      else 0
    trans settled (ℓ i)
    · dsimp only [settled,ℓ,packets]
      split <;> rename_i h
      · cases he : atRow C k p O Y Q hm X (N:=N) μ (layout C k (G:=G) (e:=e) i) <;> rfl
      · simp
    · cases ℓ i with
      | inl a => rfl
      | inr b => simp [settled,atRow]
  · apply present C k p O Y Q hm X μ (fun _ _ t =>
      point.B * (coverNumber point.B t.plot : ℝ) ≤ offset k (e:=e) * point.B + ((1 : ℕ) : ℝ)*t.fall)
    intro v
    let b := v.1
    have geom := WilsonMarkedAddressGeometry.centers (sprigB
      (original C k p O Q hm X (N:=N) b (actual C p b.1,v.2.1)) v.2.2) b.1.val.val
      (owner C b.1) p (placed C p b.1) (addresses C p b.1 (owner_mem C b.1))
      (fun j hj => addresses C p b.1 hj) point.B point.B_pos
    have d := degree_le C k e b
    have h := Finset.card_le_univ b.1.val.val
    have off : 1+2*b.2.2.val+6*b.1.val.val.card ≤ offset k (e:=e) := by unfold offset; omega
    have fin := geom.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ off) _)
    change (point.B:ℝ)*(coverNumber point.B (T v).plot:ℝ) ≤
      (offset k (e:=e):ℝ)*point.B+((1:ℕ):ℝ)*(T v).fall
    simpa only [Nat.cast_one,one_mul,mul_comm ((offset k (e:=e)):ℝ)] using
      (show (point.B:ℝ) * (coverNumber point.B (T v).plot : ℝ) ≤
          (point.B:ℝ) * offset k (e:=e) + (T v).fall from by exact_mod_cast fin)

/-- One common paid realization before root placements and all external
test data. The coupling may be set to one or to the actual regulator. -/
theorem issued (hA : 0≤A) (hN : m<N) (closed : Cloze (NativeMarkedAddressTokens.axes O) k Q Credit.leanC)
    (tickets : Insure (Fintype.card V) (mass k Finset.univ) Q Credit.leanC) :
    ∃ M : RootedMeasures C k O (e:=e) (G:=G),
      rootedSale C k O Q hm X (N:=N) M ∧
      ∀ (n : Side) (p : V→Site n) (Y : V→Dip), (∀ v,(Y v).Fits (O v).field) →
        let μ := sampled C k p O M
        let P := packets C k p O Y Q hm X (N:=N) μ
        ∀ (point : BudgetPoint) (w : V→ℝ) (g s : ℝ), (∀ v,0<w v) →
          0<s → s≤width k Q hm → point.supportExponent / point.B ≤ s / 4 →
          P.Paid point (fun v => {p v}) (OriginalMeasuredSourceRows.region O Y (fun v => {p v}))
            w g s (budget C k O Q hm (A:=A) w g) (offset k (e:=e)) 1 := by
  obtain ⟨M,charge⟩ := preselected C k O Q hm X hA hN closed tickets
  refine ⟨M,charge,?_⟩
  intro n p Y fits μ P point w g s hw hs hsmall hspace
  obtain ⟨raw,caps⟩ := purchase C k p O Y Q hm X (N:=N) M charge
  exact paidAt C k p O Y Q hm X μ fits raw caps point w hw g s hs hsmall hspace

end YM.Integration.OriginalFundedMarkedPackets
end
