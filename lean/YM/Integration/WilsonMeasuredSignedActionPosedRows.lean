import YM.Integration.WilsonMeasuredSignedActionPosed

/-! A reposed finite physical bank at the same thermal precision on both arrays. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option warningAsError true
set_option quotPrecheck false
namespace YM.Integration.WilsonMeasuredSignedActionPosedRows
open PhysicalNext.Repeat.Legato
open Filter Set Finset Wilson Table PhysMS PhysMS.Frame Trace Trace.Pilot Climb
open scoped Classical Topology BigOperators
open WilsonMeasuredSignedActionPosed (move restored)
variable {G:Gauge}{R:Run G}{S:Table R.family.book}{n:ℕ}{d:Caps n}
local notation "D" i => (Bel R.family.book).Field (d i)

def mass {k:Fin n→ℕ}(B:∀i,Module.Basis (Fin (k i)) ℂ (D i))(v:∀i,D i):ℝ:=
  ∏ i,∑ a,‖(B i).repr (v i) a‖

theorem finite {k:Fin n→ℕ}(B:∀i,Module.Basis (Fin (k i)) ℂ (D i))
    (M N:MultilinearMap ℂ (fun i=>D i) ℂ)(v:∀i,D i){ε:ℝ}
    (fee:∀a:(i:Fin n)→Fin (k i),‖M (fun i=>B i (a i))-N (fun i=>B i (a i))‖≤ε):
    ‖M v-N v‖≤ε*mass B v:=by
  let t:∀i,Fin (k i)→ℂ:=fun i=>fun a=>(B i).repr (v i) a
  let A:=M-N
  have expand:A v=∑ a:(i:Fin n)→Fin (k i),(∏i,t i (a i)) • A (fun i=>B i (a i)):=by
    have arg:v=fun i=>∑a:Fin (k i), t i a • B i a:=funext fun i=>((B i).sum_repr (v i)).symm
    calc
      A v=A (fun i=>∑a:Fin (k i),t i a • B i a):=congrArg A arg
      _=_:=by
        rw [MultilinearMap.map_sum]
        apply sum_congr rfl
        intro a _
        rw [MultilinearMap.map_smul_univ]
  change ‖A v‖≤_
  rw [expand]
  calc
    _≤∑ a:(i:Fin n)→Fin (k i),‖(∏i,t i (a i)) • A (fun i=>B i (a i))‖:=norm_sum_le ..
    _≤∑ a:(i:Fin n)→Fin (k i),(∏i,‖t i (a i)‖)*ε:=by
      apply sum_le_sum
      intro a _
      rw [norm_smul,norm_prod]
      exact mul_le_mul_of_nonneg_left (fee a) (prod_nonneg fun _ _=>norm_nonneg _)
    _=ε*mass B v:=by
      rw [←sum_mul,mul_comm]
      exact congrArg (ε * ·) (Fintype.prod_sum (fun i a=>‖t i a‖)).symm

theorem original {k:Fin n→ℕ}(B:∀i,Module.Basis (Fin (k i)) ℂ (D i))
    (M N:MultilinearMap ℂ (fun i=>D i) ℂ)(J Q:Fin n→tower S)(v:∀i,D i){ε:ℝ}
    (fee:∀a:(i:Fin n)→Fin (k i),‖M (fun i=>B i (a i))-N (fun i=>B i (a i))‖≤ε):
    let y:=fun i=>move (R:=R) (J i) (Q i) (d i) (v i)
    (∀i,J i (d i) (y i)=Q i (d i) (v i)) ∧ ‖M y-N y‖≤ε*mass B y:=
  ⟨fun _=>restored (R:=R) _ _ _ _,finite B M N _ fee⟩

theorem fixed {k:Fin n→ℕ}(B:∀i,Module.Basis (Fin (k i)) ℂ (D i))
    {Γ:Type*}{ω:Filter Γ}(J Q:ℝ→tower S)(near:localCost trail J Q)
    (ρ:Fin n→Γ→ℝ)(ends:∀i,Tendsto (ρ i) ω trail)(v:∀i,D i):
    Tendsto (fun p=>mass B (fun i=>move (R:=R) (J (ρ i p)) (Q (ρ i p)) (d i) (v i)))
      ω (𝓝 (mass B v)):=by
  unfold mass
  apply tendsto_finsetProd
  intro i _
  apply tendsto_finsetSum
  intro a _
  have h:=((B i).coord a).continuous_of_finiteDimensional.continuousAt (x:=v i)
  exact ((h.tendsto.comp ((near (d i) (v i)).comp (ends i)))).norm

end YM.Integration.WilsonMeasuredSignedActionPosedRows
end
