import YM.Integration.WilsonMeasuredPublicEntranceTrialLamp

/-! A returned one-name trial keeps its original support and its original
field when charged at the common wallet of its actual spectators. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTrialTariff
open Function Finset Lattice Wilson RG Ac Marker Push Source Labels QuadraticLocal
open Push.Local Push.AbsoluteSums Extra.Histories MergeProof MergeProof.Accent
open WilsonMeasuredPublicEntranceTrialLamp
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:Side}{p:BudgetPoint}{V I X:Type}[Fintype V][DecidableEq V]{o:V→Site n}{J:Census V}
variable (A:Lamps X I G p o J)(v:V)(x:X)
local notation "L" => leaf A v x

omit [Fintype V] in
theorem rebill {w:V→ℝ}(μ:V→ℝ)(wv:0<w v)(mv:0≤μ v){e m:ℝ}(sale:A.Paid w p.B e m):
    (L).Paid μ p.B e (μ v/w v*m):=by
  obtain ⟨b,nn,der,price⟩:=(paid A v x sale).budget
  refine ⟨b,nn,der,?_⟩
  have scaled:=AnalyticBridge.VerifiedReset.Quotes.hit_scale (div_nonneg mv wv.le) price
  have rows(i):μ v/w v*(Poly.toll w ((L).mode i)*b i)=Poly.toll μ ((L).mode i)*b i:=by
    rw [lanes A v x i]
    simp only [Poly.toll,Census.fire,prod_singleton]
    field_simp
  rwa [funext rows] at scaled

theorem original [Countable I](w μ:V→ℝ)(wp:∀i,0<w i)(mp:∀i,0<μ i)
    {e m:ℝ}(nn:0≤e)(sale:A.Paid w p.B e m):
    ∃ (c:Poly J)(M:Support n → Config G n → Poly J),
      c.part J.quiet=0 ∧ Poly.price μ c≤(Fintype.card V:ℝ)*(μ v/w v*m) ∧
      (∀Z,Burns o Z (M Z) p.threshold) ∧ Towed μ id M p.B e (μ v/w v*m) ∧
      ∀U,Poly.send (J.fire v) ((A.log x U).part (J.fire v))=c+∑Z,M Z U:=by
  obtain ⟨c,M,quiet,fee,localFields,spent,seen⟩:=grouped L v () μ mp nn
    (rebill A v x μ (wp v) (mp v).le sale)
  refine ⟨c,M,quiet,fee,localFields,spent,fun U=>?_⟩
  have eq:=seen U
  rwa [read A v x wp nn sale U,Poly.part_send,if_pos rfl] at eq

end YM.Integration.WilsonMeasuredPublicEntranceTrialTariff
end
