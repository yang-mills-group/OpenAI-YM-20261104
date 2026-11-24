import YM.Integration.FVA1Physical.Marked.FundedLedger

/-! Obtain a positive common source aperture from the actual support bill,
then transfer the funded finite ledger to arbitrary signed input amplitudes.
The support bill and the re-inflation factors stay visible. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Filter Function Lattice RG Pressure Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure ConnectedActivityE6
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AnalyticBridge VerifiedReset Collection
open Progress.DirectedRecipe Roof Extra.Iteration Time ThroughLaunch Roost JointLoad RGComparison.Core16
open RGComparison01 RGComparison01.Pledge Holdings Merge Qlocal Qlocal.Parabola
open AllOrder Transit WheelP Floe Floe.Step.PlanV Push.PriceCompiler RG.Supply Input Org
open MeasureTheory Canopy Leasing Marker Extra.Trajectories Comparison.RG02.Order
open scoped BigOperators Classical Topology
section Admission
variable {G : Gauge} {f : Side} {R : Rep G f} {ι : Type} [Fintype ι] (M : ι→Lotus.Leaf R)

/-- Common scale including the complete undiluted support bill, even when
every assigned source anchor coincides. -/
def commonAperture (mass : ℝ) := mass/(1+∑ i,(M i).weight * Real.exp (R.p.supportExponent * coverNumber R.p.B (M i).crest))

theorem common_aperture (regular : Staircase.grows M) {mass : ℝ} (hm : 0 < mass) :
    0 < commonAperture M mass ∧ Bench M (fun _=>commonAperture M mass) mass := by
  let fee := fun i => (M i).weight * Real.exp (R.p.supportExponent * coverNumber R.p.B (M i).crest)
  let total := ∑ i,fee i
  have nn (i) : 0≤fee i := mul_nonneg (M i).profit (Real.exp_nonneg _)
  have ht : 0≤total := Finset.sum_nonneg (fun i _=>nn i)
  let a := commonAperture M mass
  have ha : 0<a := div_pos hm (by linarith : 0 < 1+total)
  have room : a*total ≤ mass := calc
    a*total ≤ a*(1+total) := mul_le_mul_of_nonneg_left (by linarith) ha.le
    _ = mass := div_mul_cancel₀ _ (by linarith : 1+total ≠ 0)
  have seats (i) : ∃ o,o∈(M i).crest := by
    obtain ⟨j,hj⟩ := regular i
    refine ⟨(R.activities.reg j).site,?_⟩
    change _∈(M i).turn.support R
    rw [hj]
    exact (R.activities.reg j).anchor
  choose o ho using seats
  refine ⟨ha,o,ho,fun _=>ha.le,fun v=>?_⟩
  apply budget_finite
  · intro i
    split
    · exact mul_nonneg (mul_nonneg ha.le (M i).profit) (Real.exp_nonneg _)
    · exact le_rfl
  · apply le_trans _ room
    change _ ≤ a * ∑ i,fee i
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    split
    · exact (mul_assoc ..).le
    · exact mul_nonneg ha.le (nn i)
end Admission

variable {G : Gauge} {X : Run G} {z N n k m : ℕ} {path : ℕ → Floe.Layout G} {Γ : ℕ → Pace.Coin}
    {x : (i : ℕ) → Rep G (X.alloy.B.a.S.side i n)}
    (track : Metre X.alloy X.kit X.T path Γ z N n k x) (lo : z ≤ m) (hi : m < N)
    (T : Slices X.family.path.levels n)
    {ι : Type} [Fintype ι] (M : ι→Lotus.Leaf (x (m+1))) (g : ι→ℝ)
    (H : Opera.Guide X.alloy.B X.kit.shape N m n (x (m+1)))
    (hH : Opera.Price X.alloy.B X.kit.shape N m n (x (m+1)) H)
    {k₀ j₀ : ℕ} (η : ℕ→ℝ) (B₀ : Bauble G (X.rolls.L (X.alloy.B.a.clock.J (m+1))))
    (funds : Opened X.kit η k₀ j₀ m B₀)
    (regular : Staircase.grows M) (inj : Injective fun i => (M i).turn)
local notation "p" => X.alloy.B.a.budget m
local notation "χ₀" => Chi.canonical
local notation "op" => X.family.path.levels.clock.op m n

omit [Fintype ι] in
theorem source_moment_dilate (a b : ι→ℝ) (s : Finset ι) (V : Config G (X.family.side m n)) :
    source_path_moment hi T M (a*b) s V = (∏ i∈s,a i) * source_path_moment hi T M b s V := by
  let v := ∏ i∈s,a i
  let f := fun u => (traversal T hi).vacuum (G:=G) (line X.family.path n (m+1) N) u *
    ((∏ i∈s,b i) * ∏ i∈s,(M i).ingredient u)
  let β := X.family.path.β N n (m+1)
  let Z := (traversal T hi.le).vacuum (G:=G) (line X.family.path n m N) V
  have push : (op).push β (fun u=>v*f u) V = v*(op).push β f V := by
    unfold StepData.push
    simp only [smul_eq_mul,mul_left_comm _ v,integral_const_mul]
  unfold source_path_moment
  simp only [Pi.mul_apply,Finset.prod_mul_distrib]
  have e (u : Config G (X.family.side (m+1) n)) :
      (traversal T hi).vacuum (G:=G) (line X.family.path n (m+1) N) u *
        (((∏ i∈s,a i)*(∏ i∈s,b i)) * ∏ i∈s,(M i).ingredient u) = v*f u := by unfold v f; ring
  exact (congrArg (fun z=> (op).push β z V / Z) (funext e)).trans
    ((congrArg (· / Z) push).trans (mul_div_assoc ..))

include track lo hi hH funds regular inj in
/-- No sign restriction or Bench invoice on the wallet's actual source
amplitudes. At every degree/depth the difference from the full conditional
cumulant is the same paid bank of omitted clusters with a displayed signed
re-inflation factor. The positivity and mass of its common aperture are
derived from the actual opened lease. -/
theorem signed_low_history {d : ℕ} (ribbon : Ribbon (x (m+1)) d) (s : Finset ι) (hs : s.Nonempty)
    (degree depth : ℕ) (V : Config G (X.family.side m n)) (clear : flags (p).threshold V = ∅) :
    let a := commonAperture M (B₀.mass (X.alloy.B.a.clock.hatBeta m))
    let signed := ∏ i∈s,g i/a
    0<a ∧ Stowe.tale M g H (Drawing.cabinet H ribbon) degree depth s V (χ:=χ₀) +
      signed * (∑' z:Baked.Cl M H, masked (p).threshold (Baked.origins M H z)
        (Bridges.balance M (fun _=>a) H ribbon degree depth s (χ:=χ₀) z) V) =
      Button.Earmark (fun t=>source_path_moment hi T M g t V) (Fintype.card ι) s := by
  intro a signed
  have hm := (funds.paid _ (X.alloy.B.valid.pays m)).permission.crucial
  obtain ⟨ha,admittedMass⟩ := common_aperture M regular hm
  let A := fun i=>g i/a
  let b := fun _:ι=>a
  have split : A*b=g := funext fun i=> div_mul_cancel₀ _ ha.ne'
  let Z := Drawing.cabinet H ribbon
  have table : (fun t=>source_path_moment hi T M g t V) =
      Button.polish A (fun t=>source_path_moment hi T M b t V) := by
    funext t
    rw [←split]
    exact source_moment_dilate hi T M A b t V
  have logs := low_ledger_history track lo hi T M b H hH η B₀ funds admittedMass regular inj ribbon s hs degree depth V clear
  let incl := Function.Embedding.refl ι
  have select := Stowe.picture M g H Z incl s degree depth A b (χ:=χ₀) (show g ∘ incl=A*b from split.symm)
  have scale : Stowe.tale M g H Z degree depth s V (χ:=χ₀) =
      signed * Stowe.tale M b H Z degree depth s V (χ:=χ₀) := by
    have same : M ∘ incl=M := rfl
    rw [same] at select
    simpa only [incl,Finset.map_refl,Pi.smul_apply,smul_eq_mul] using congrFun select V
  refine ⟨ha,?_⟩
  rw [table,←Button.tonal]
  change _ = signed * _
  change Stowe.tale M g H Z degree depth s V (χ:=χ₀) + signed*_ = _
  rw [scale,←mul_add,logs]
end YM.Integration.FVA1Physical.Marked
