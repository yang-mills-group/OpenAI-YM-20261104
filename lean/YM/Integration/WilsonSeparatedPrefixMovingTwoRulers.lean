import YM.Integration.WilsonSeparatedPrefixMovingLenses
import YM.Integration.WilsonSeparatedPrefixMovingCalendar

/-! The same physical margin buys the two native ruler tests across the
inner capture. Only the actual near-to-capture ratio enters the unit price. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingTwoRulers
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Function Matrix Lattice RG Laurent Bloch Blue FreeResolvent Work.F08 Bank Wilson Tree Power Source
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped Classical Topology

theorem original {D:ℕ}(S:Schedule)(t b m:ℕ)(fine:b ≤ m)(ψ:Rarity D)(y gap r:ℝ):
    let T:=paceT S m t
    let T_b:=paceT S b t
    let l:=paceT S m b
    let v:=y/l
    2+2*|y| ≤ r → ψ.radius+|y/T|+1 ≤ r →
    (∀z∈tsupport ψ.ψ.val,T*gap+max r (l+|y|) ≤ ‖T • z‖) →
    (∀z∈tsupport ψ.ψ.val,T*gap+r ≤ ‖T • z‖) ∧
    2+2*|v| ≤ r ∧ ψ.radius+|v/T_b|+1 ≤ r ∧
    (∀z∈tsupport ψ.ψ.val,T_b*gap+1+|v| ≤ ‖T_b • z‖):=by
  intro T T_b l v centered farBox remote
  have l1:1 ≤ l:=pace_ge S fine
  have lp:0<l:=pace_pos ..
  have bp:0<T_b:=pace_pos ..
  have product:T=l*T_b:=by
    dsimp only [T,l,T_b,paceT];field_simp [(S.a_pos b).ne']
  have scaled:v/T_b=y/T:=by dsimp only [v];rw [div_div,←product]
  have absEq:|v|=|y|/l:=by dsimp only [v];rw [abs_div,abs_of_pos lp]
  refine ⟨fun z hz=>by linarith only [le_max_left r (l+|y|),remote z hz],?_,?_,?_⟩
  · rw [absEq]
    linarith only [centered,div_le_self (abs_nonneg y) l1]
  · simpa only [scaled] using farBox
  · intro z hz
    have paid:T*gap+(l+|y|) ≤ ‖T•z‖:=by linarith only [le_max_right r (l+|y|),remote z hz]
    have lhs:l*(T_b*gap+1+|v|)=T*gap+(l+|y|):=by rw [absEq,product];field_simp [lp.ne'];ring
    have rhs:l*‖T_b•z‖=‖T•z‖:=by simp only [product,mul_smul,norm_smul,Real.norm_eq_abs,abs_of_pos lp]
    exact (mul_le_mul_iff_right₀ lp).mp (lhs.trans_le (paid.trans_eq rhs.symm))

end YM.Integration.WilsonSeparatedPrefixMovingTwoRulers
