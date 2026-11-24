import YM.Integration.WilsonConditionalTaylorVacuumWindingDeposit
import YM.Integration.WilsonUniformUnmarkedSpatialLimit

/-! Spend the signed winding bound, for the real physical period,
on every occupied kernel of the folded conditional vacuum. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelCoilLimit
open Function Filter Lattice RG Wilson Precision Laurent Bloch Next.Foundations WilsonCoeffUV.Bank.Ticket
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Blue ActualRunAdmissionScales
open scoped Classical Topology BigOperators
variable {G:Gauge}

theorem single {n:Side} {r:ℕ} {s:ℝ} (hs:0 ≤ s)
    (P:Ten ℝ (Co n (Hooks G)) (r+1)) (x:dock (Site n) (Hooks G) (r+1)):
    |P x|≤RootedVacuumWinding.held (0:Fin (r+1)) (x 0) s P:=by
  classical
  have base:1≤Real.exp (s*(soar (tor n) x:ℝ)):=Real.one_le_exp (mul_nonneg hs (Nat.cast_nonneg _))
  have term:=Finset.single_le_sum (f:=fun y:dock (Site n) (Hooks G) (r+1)=>
    if y 0=x 0 then Real.exp (s*soar (tor n) y)*‖P y‖ else 0)
    (fun y _=>by split_ifs <;> positivity) (Finset.mem_univ x)
  rw [if_pos rfl,Real.norm_eq_abs] at term
  exact le_trans (le_mul_of_one_le_left (abs_nonneg _) base) term

variable (R:Run G) (simple:G.Simple)
include simple in
theorem original {E e r c q degree j:ℕ} {width:Gear G→ℝ}
    (positive:∀I,0<width I) (Q:Realm G (E+1) Credit.leanC) (here:Q.anchor≤j)
    (receipt:RootedVacuumWinding.ReceiptOn R E e r c q degree width j Q here)
    (N:ℕ) (live:j<N) (x:dock Cover (Hooks G) (r+1)):
    Tendsto (fun per:ℕ=>coil0 R.family.path.levels R.metals.O j N (R.family.side j per) e (r+1)
        (foldUnder (R.family.side j per) ∘ x)) atTop
      (𝓝 (freshet R.family.path.levels R.metals.O N j e (r+1) x)):=by
  let A:=R.family.path.levels
  let O:=R.metals.O
  let n:=R.family.side j
  let s:=width (Q.mint j here).gear
  have sPos:0<s:=positive _
  let M:ℝ:=(admittedCost A j)^degree
  let fine (p:ℕ):=RootedVacuumWinding.ground A O N j (n p) e r (foldUnder (n p) ∘ x)
  have raw:∀p,|fine p|≤M*Real.exp (-(s/4)*((n p).val:ℝ)):=by
    intro p
    obtain ⟨B,_,tail,held⟩:=receipt N p live
    exact (single sPos.le _ _).trans ((held 0 ((foldUnder (n p) ∘ x) 0)).trans tail)
  have growth:Tendsto (fun p:ℕ=>(n p).val) atTop atTop:=
    (show StrictMono (fun p:ℕ=>(n p).val) from fun _ _ h=>
      Nat.mul_lt_mul_of_pos_right (R.family.S.period_strict h) (R.family.S.denominator j).pos).tendsto_atTop
  have pay:Tendsto (fun p:ℕ=>Real.exp (-(s/4)*((n p).val:ℝ))) atTop (𝓝 0):=
    Real.tendsto_exp_atBot.comp ((tendsto_natCast_atTop_atTop.comp growth).const_mul_atTop_of_neg (by linarith))
  have small:Tendsto fine atTop (𝓝 0):=by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Real.norm_eq_abs]
    apply squeeze_zero (fun p=>abs_nonneg _) raw
    simpa using pay.const_mul M
  have base:=(perch A O simple R.alloy.B.ratio live).growth e (r+1)
  obtain ⟨σ,C,σpos,cover⟩:=base.cover
  have lens:=((lagoon_yields cover σpos base.road).point x).comp (WilsonUniformUnmarkedSpatialLimit.sides R j)
  simp only [dilute,if_neg (Nat.succ_ne_zero _)] at lens
  have together:=lens.sub small
  rw [sub_zero] at together
  apply together.congr'
  filter_upwards [] with p
  let a:=lagoon (freshet A O N j e (r+1)) (n p) (foldUnder (n p) ∘ x)
  let b:=coil0 A O j N (n p) e (r+1) (foldUnder (n p) ∘ x)
  change a - (a-b)=b
  exact sub_sub_cancel a b

end YM.Integration.WilsonConditionalTaylorWheelCoilLimit
end

