import YM.Integration.WilsonMarkedIndependentFiniteSourceSlope
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! The whole continuous-dual marked tensor is transported on the same real finite
Wilson conditional, with its true quiet discrepancy and original signed input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentFiniteVectorSlope
open Function Finset Lattice Laurent Wilson RG Precision Tree Bloch Exterior WilsonCoeffUV
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding
open WilsonVacuumPreResetFiniteHeatWindow (horizon)
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open scoped Classical BigOperators

theorem original (G:Gauge)(e i l r:ℕ)(hi:i ≤ e):
    ∃(v:Gear G→ℝ)(d:ℕ)(C:ℝ),1 ≤ C ∧ ∀Q:Realm G (e+1) Credit.leanC,∀m (hm:Q.anchor ≤ m),
      v (Q.mint m hm).gear ≤ Q.cash Credit.leanC m → ∀N (live:m<N) n,
        let p:=cloVent Q m N n hm live 1 zero_lt_one
        let f:=p.n*(holt Q m hm 1 zero_lt_one).P.L
        let previous:=(story Q.draws Q.paid N (m+1)).1 f
        ∀(V:Type)[NormedAddCommGroup V][NormedSpace ℝ V],∀T U:Pal V (Woods G f),∀η δ A:ℝ,0<η → η ≤ 1 → 0<δ → 0<A →
        (∀j ≤ e,∀h ≤ horizon e (r+2*l),∀x,|previous j h x-p.W' j h x| ≤ η) →
        (∀j ≤ e,∀h ≤ horizon e (r+2*l),∀x,‖T j h x-U j h x‖ ≤ δ) →
        (∀j ≤ e,∀h ≤ horizon e (r+2*l),∀x,‖U j h x‖ ≤ A) →
        ∀x,‖reed p.wheel p.shadow p.H (p.T p.n) Q.paid previous l T i r x-
          reed p.wheel p.shadow p.H (p.T p.n) Q.paid p.W' l U i r x‖ ≤
          C*(gross (Q.y m) f)^d*(δ+A*η):=by
  obtain ⟨v,d,C,hC,scalar⟩:=WilsonMarkedIndependentFiniteSourceSlope.original G e i l r hi
  refine ⟨v,d,C,hC,?_⟩
  intro Q m hm cash N live n p f previous V vAdd vNorm T U η δ A positive small dpos apos prior changed marked x
  let a:=reed p.wheel p.shadow p.H (p.T p.n) Q.paid previous l T i r x
  let b:=reed p.wheel p.shadow p.H (p.T p.n) Q.paid p.W' l U i r x
  obtain ⟨L,unit,read⟩:=exists_dual_vector'' ℝ (a-b)
  let Z(T:Pal V (Woods G f)):=ply L.toLinearMap T
  have inside(z:V):|L z|≤‖z‖:=by
    simpa only [←Real.norm_eq_abs,one_mul] using
      (L.le_opNorm z).trans (mul_le_mul_of_nonneg_right unit (norm_nonneg z))
  have act:∀j ≤ e,∀h ≤ horizon e (r+2*l),∀z,|(Z T) j h z-(Z U) j h z|≤δ:=by
    intro j hj h hh z
    change |L (T j h z)-L (U j h z)|≤δ
    rw [←map_sub]
    exact (inside _).trans (changed j hj h hh z)
  have cap:∀j ≤ e,∀h ≤ horizon e (r+2*l),∀z,|(Z U) j h z|≤A:=
    fun j hj h hh x=>(inside _).trans (marked j hj h hh x)
  have test:=scalar Q m hm cash N live n (Z T) (Z U) η δ A positive small dpos apos prior act cap x
  have get(π:PChart G f)(V₀:Pal V (Woods G f)):
      L (reed p.wheel p.shadow p.H (p.T p.n) Q.paid π l V₀ i r x)=
        reed p.wheel p.shadow p.H (p.T p.n) Q.paid π l (Z V₀) i r x:=
    congrFun (congrFun (congrFun (reed_maps p.wheel p.shadow p.H (p.T p.n) l L.toLinearMap) i) r) x
  rw [←get,←get,←map_sub] at test
  change |L (a-b)|≤_ at test
  change L (a-b)=‖a-b‖ at read
  simpa only [read,abs_of_nonneg (norm_nonneg _)] using test

end YM.Integration.WilsonMarkedIndependentFiniteVectorSlope
end
