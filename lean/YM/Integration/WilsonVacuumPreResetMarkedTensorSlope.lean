import YM.Integration.WilsonVacuumPreResetMarkedPolynomialTable
import YM.Integration.WilsonVacuumPreResetWindingTransfer

/-! The degree bound for the whole connected marked table gives a
dimension-independent interpolation price in the actual norm of its tensor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetMarkedTensorSlope
open Function Finset Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open scoped BigOperators Classical
variable {ι:Type} {D:ι→ℕ} {G:Gauge} {I:Finset ι}

private theorem dual (F:ℝ→Pen D I)(d:ℕ)
    (faces:∀A:Case D,WilsonVacuumPreResetWindingPolynomial.At d (fun t=>touch A I (F t)))
    (L:Pen D I→L[ℝ]ℝ):WilsonVacuumPreResetWindingPolynomial.At d (fun t=>L (F t)):=by
  let S:=range (d+1)
  let v:ℕ→ℝ:=Nat.cast
  let b:=Lagrange.basis S v
  have nodes:Set.InjOn v (↑S):=by
    intro i _ j _ h
    change (i:ℝ)=(j:ℝ) at h
    exact_mod_cast h
  have assemble(t:ℝ):F t=∑j∈S,(b j).eval t • F (v j):=by
    apply pen_inj
    intro A
    obtain ⟨P,degree,read⟩:=faces A
    have deg:P.degree < (S.card:WithBot ℕ):=P.degree_le_natDegree.trans_lt (by
      rw [show S.card=d+1 from card_range ..];exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le degree))
    have formula:P.eval t=∑j∈S,P.eval (v j)*(b j).eval t:=by
      conv_lhs => rw [Lagrange.eq_interpolate (s:=S) (v:=v) (f:=P) nodes deg,
        Lagrange.interpolate_apply,Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_mul,Polynomial.eval_C,b]
    simp only [map_sum,map_smul,smul_eq_mul,←read]
    simpa only [mul_comm] using formula
  let P:=Lagrange.interpolate S v (fun j=>L (F (v j)))
  refine ⟨P,Polynomial.natDegree_le_iff_degree_le.mpr ?_,?_⟩
  · have cost:=Lagrange.degree_interpolate_le (fun j=>L (F (v j))) nodes
    simpa only [S,card_range,Nat.add_sub_cancel] using cost
  · intro t
    change P.eval t=L (F t)
    conv_rhs => rw [assemble t]
    simp only [P,Lagrange.interpolate_apply,Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,
      map_sum,map_smul,smul_eq_mul,b,mul_comm]

/-- Before choosing the period, cutoff, angular degree or the interpolation
data, one constant bounds the norm of the complete connected tensor change. -/
theorem original [DecidableEq ι] (e:ℕ)(I:Finset ι):∃C:ℝ,0≤C ∧
    ∀{c f:Side}(S:StepData c f)(F:Forest S.ratio)(H:FreeResolvent.FaceRow)
    (Q:Matrix (Body 1 f) (Body 1 c) ℝ)(O:ChartRatio G)(P V:PChart G f)
    (K B:family G D)(reset:Cost)(k:ι→ℕ)(r:ℕ)(x:Fin r→Woods G c)(M t:ℝ),
    0≤M→0≤t→t≤1→
    (∀u:ℝ,|u|≤1→‖mist S F H Q O (P+u•V) (fun J=>K J+u•B J) reset k I e r x‖≤M)→
    ‖mist S F H Q O (P+t•V) (fun J=>K J+t•B J) reset k I e r x-
      mist S F H Q O P K reset k I e r x‖≤C*M*t:=by
  obtain ⟨C,nn,price⟩:=WilsonVacuumPreResetWindingTransfer.observed (e+I.card)
  refine ⟨C,nn,?_⟩
  intro c f S F H Q O P V K B reset k r x M t nonneg lo hi paid
  let Y(t:ℝ):=mist S F H Q O (P+t•V) (fun J=>K J+t•B J) reset k I e r x
  obtain ⟨L,unit,read⟩:=exists_dual_vector'' ℝ (Y t-Y 0)
  obtain ⟨p,degree,fit⟩:=dual Y (e+I.card)
    (fun A=>WilsonVacuumPreResetMarkedPolynomialTable.original S F H Q O P V K B reset k A I e r x) L
  have billed(u:ℝ)(hu:|u|≤1):|p.eval u|≤M:=by
    rw [fit,←Real.norm_eq_abs]
    exact ((L.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) unit)).trans (paid u hu)
  have bound:=price p M t degree nonneg lo hi billed
  rw [fit,fit,←map_sub] at bound
  change L (Y t-Y 0)=‖Y t-Y 0‖ at read
  rw [read,abs_of_nonneg (norm_nonneg _)] at bound
  simpa only [Y,zero_smul,add_zero] using bound

end YM.Integration.WilsonVacuumPreResetMarkedTensorSlope
end
