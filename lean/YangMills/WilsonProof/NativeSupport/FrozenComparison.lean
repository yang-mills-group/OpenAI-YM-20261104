import YangMills.WilsonProof.NativeSupport.FrozenWord
import YangMills.WilsonProof.NativeSupport.FrozenCalendar

/-! All-period original conditional thermal comparison of two genuine
seated source words. Inlet span and offset receipts have exactly the
numeric conclusions of the frozen source theorems. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Filter Finset Lattice RG Wilson RGComparison.Core16 PhysicalNext.Repeat.Legato
open Pert.Asymptotics Next.Foundations Labels
open scoped Classical BigOperators Topology
variable {G : Gauge} {I : Type} [Fintype I] [DecidableEq I]

def wordAt {n : Side} (grade : I→ℕ) (label : (i:I) → ((frames G).level (grade i)).Index)
    (a : I→Site n) (b : Bool) (U : Config G n) := component b (∏ i,atom grade label a i U)

theorem original_thermal (R : Run G) (simple : G.Simple)
    (slow : ∀ j, ((R.alloy.B.a.budget j).supportExponent+1)*
      (((R.alloy.B.a.S.block (j-1)).val:ℝ)^4) ≤ Real.sqrt (R.alloy.B.a.clock.hatBeta j))
    (grade : I→ℕ) (label : (i:I) → ((frames G).level (grade i)).Index)
    (s W Q : ℕ) (stencils : ∀ i,minSide G (grade i) ≤ s) (wanted : 1≤Q) :
    ∀ᶠ k:ℕ in atTop, ∀ t N, k≤t → ∀ ht:t<N,
      ((N-t:ℕ):ℝ)*Real.log 3 ≤ R.family.S.scale N-R.family.S.scale t →
      R.family.S.scale N-R.family.S.scale t ≤ (W:ℝ)*Real.log (R.alloy.B.a.clock.hatBeta N) →
      ∀ per, ∀ T:Slices R.family.path.levels per, ∀ a e : I → Site (R.family.side N per), ∀ b : Bool,
      ∀ p, 2*halfOrder W Q≤p → ∀ v : ℕ → ℝ,
        let d:=traversal T ht.le
        let B:=RGComparison.Core16.line R.family.path per t N
        let Y:=WilsonUniformUnmarkedInletSignedResponse.line B v 1
        let g:=regulatorRun R.family N per N
        let Z:=fun U=>wordAt grade label a b U-wordAt grade label e b U
        v d.depth=0 → (∀ j,0<j → j<d.depth → |v j| ≤ g^p) →
        |d.conditioned Y Z 1-d.conditioned B Z 1| ≤ 6*2^(Fintype.card I)*bill grade G*2^Q*g^(2*Q) := by
  let A:=R.alloy.B.a
  obtain ⟨i,heat⟩:=eventually_atTop.mp ((Next.Rank.Station.hat_rate A simple).eventually_ge_atTop 2)
  filter_upwards [eventually_ge_atTop i,uniform_dates R simple (Fintype.card I) s W Q] with k ki paid
  intro t N kt ht lower upper per T a e b p order v d B Y g Z top offset
  let x:=height R N
  have kN:=kt.trans ht.le
  have price:=paid N kN
  obtain ⟨bc,ec,dc,steps,roof⟩:=calendar_expenses R simple T ht.le W slow lower upper
  have hot:=heat N (ki.trans kN)
  have g0 : 0≤g := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have fee:=actual_fee R N per W Q p hot order
  let m:=Fintype.card I
  let ε:=((x:ℝ)^Q)⁻¹
  have one (o : I→Site (R.family.side N per)) :
      |mean d Y (wordAt grade label o b) 1-mean d B (wordAt grade label o b) 1| ≤ 2^m*bill grade G*(3*ε) := by
    apply word_cost d (traversal_ok T ht.le) Y B grade label o b s stencils
    intro F c sU htF localF
    exact paid_pattern R simple T ht F o s W Q x c sU htF localF v (pow_nonneg g0 _) top offset
      price.1 wanted bc ec dc steps roof price.2.1 price.2.2 fee
  have cont (o : I→Site (R.family.side N per)) : Continuous (wordAt grade label o b) :=
    (component b).continuous.comp (continuous_finsetProd _ fun i _=>(localSection G (grade i)).continuous_places _ _)
  have sym (o : I→Site (R.family.side N per)) : GaugeInvariant (wordAt grade label o b) := fun j U=>
    congrArg (component b) (prod_congr rfl fun i _=>(localSection G (grade i)).placed_invariant (sound G _) _ _ j U)
  have eq (γ : ℕ→ℝ) : d.conditioned γ Z 1=mean d γ (wordAt grade label a b) 1-mean d γ (wordAt grade label e b) 1 :=
    (WilsonUniformUnmarkedInletConnectedCovariance.fraction d (traversal_ok T ht.le) γ 1
      ((cont a).sub (cont e)) (fun j U=>congrArg₂ (·-·) (sym a j U) (sym e j U))).trans
      (mean_difference d (traversal_ok T ht.le) γ 1 _ _ (cont a) (cont e))
  have B0 : 0<R.family.path.β N per N := lt_of_lt_of_le
    (half_pos (zero_lt_one.trans (A.fits.delayed N))) (R.T.choice.represents N per N le_rfl).band.1
  have hx : 0<(x:ℝ) := (zero_lt_one.trans (A.fits.delayed N)).trans_le (Nat.le_ceil _)
  have hβ : R.family.path.β N per N ≤ 2*(x:ℝ) :=
    (R.T.choice.represents N per N le_rfl).band.2.trans (mul_le_mul_of_nonneg_left bc (by norm_num))
  have scaleE : ε ≤ 2^Q*g^(2*Q) := by
    have low : (x:ℝ)⁻¹ ≤ 2*g^2 := by
      change (x:ℝ)⁻¹≤2*(Real.sqrt (R.family.path.β N per N))⁻¹^2
      rw [inv_pow,Real.sq_sqrt B0.le,inv_eq_one_div,←div_eq_mul_inv,div_le_div_iff₀ hx B0,one_mul]
      exact hβ
    change ((x:ℝ)^Q)⁻¹≤_
    rw [←inv_pow,pow_mul,←mul_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hx.le) low _
  have bp : 0≤bill grade G := prod_nonneg fun i _=>(zero_le_one.trans (atom_one G _))
  rw [eq Y,eq B,sub_sub_sub_comm]
  calc _ ≤ |mean d Y (wordAt grade label a b) 1-mean d B (wordAt grade label a b) 1|+
             |mean d Y (wordAt grade label e b) 1-mean d B (wordAt grade label e b) 1| := abs_sub .. 
       _ ≤ 2^m*bill grade G*(3*ε)+2^m*bill grade G*(3*ε) := add_le_add (one _) (one _)
       _ = (6*2^m*bill grade G)*ε := by ring
       _ ≤ (6*2^m*bill grade G)*(2^Q*g^(2*Q)) := mul_le_mul_of_nonneg_left scaleE (by positivity)
       _ = _ := by ring

end YM.Integration.InletSusceptibility.Packet
