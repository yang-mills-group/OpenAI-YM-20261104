import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionDividedNetworkRate
import YM.QuadraticLocal.Lamps

/-! The normalized hard row of the original funded Gallery on its own positive
vacuum, under an arbitrary original path law bearing the nominated marginal.
No separate graph, source-locality, or absolute actor-summability invoice is
assumed. The sole retained hard term has an active long physical actor. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Set Finset MeasureTheory Lattice RG Wilson Marker QuadraticLocal
open QuadraticLocal.Fusion.Attached Extra.Trajectories Push.AbsoluteSums.Animals
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V T I:Type}[DecidableEq V][Fintype V]{J:Census V}
  {o:V→Site n}{P:Rep G n}(A:Gallery T I o P J)

abbrev filedRow (t:T)(s:J.Mode)(U:Config G n):ℂ:=
  (connected (((P.activities.gas P.p U:ℂ)⁻¹) • A.gas t U)).part s

omit [Fintype V] in
theorem filed_actor_stock {w:V→ℝ}{e c:ℝ}(wp:∀v,0<w v)(paid:A.K.Paid w P.p.B e c)
    (en:0≤e)(t:T)(U:Config G n):Summable fun i=>Poly.price w (A.K.hard t i U):=by
  obtain ⟨f,rows,hits⟩:=paid.wages
  have gross:=(RG3.Letters.Frame.from_hit P.p.B e c (fun i=>Poly.price w (f i))
    (fun i=>(P.activities.forced i).inventory_ne.mono (P.activities.forced i).inventory_sup)
    (fun i=>Poly.nonnegative wp (f i)) en hits).2.1
  exact gross.of_nonneg_of_le (fun i=>Poly.nonnegative wp (A.K.hard t i U))
    (fun i=>(rows i t U).reprice _ wp)

theorem filed_long_hearing {Z:Type*}[MeasurableSpace Z](law:Measure Z)[IsFiniteMeasure law]
    (μ:Measure (Config G n))[IsFiniteMeasure μ](π:Z→Config G n)(πm:Measurable π)
    (original:Measure.map π law=μ)(live:∀z,0<P.eval (π z))
    (w:V→ℝ)(wp:∀v,0<w v)(e c:ℝ)(paid:A.K.Paid w P.p.B e c)(en:0≤e)
    (t:T)(s:J.Mode)(a b:V)(usedA:a∈s.val)(usedB:b∈s.val)(m D:ℕ)(many:0<m)
    (apart:2*m*width P.p D<separation (o a) (o b))
    (x κ M:ℝ)(xp:1≤x)(kp:0≤κ)(k1:κ≤1)(mp:0≤M)(d q h:ℕ)
    (rare:∀L:Support n,μ.real {U|L⊆flags P.p.threshold U}≤((x⁻¹)^(2*(d+q))*κ^(2*h))^L.card)
    (δ:Z→ℂ)(δm:Measurable δ)(τ ε:ℝ)(tp:0≤τ)(ep:0≤ε)
    (cap:∀z,‖(τ:ℂ)*δ z‖≤M*x^d)
    (regular:∀Y:Z→ℂ,MemLp Y 2 law →
      let f:=fun z=>Y z*(δ z-filedRow A t s (π z))
      Integrable f law ∧ τ*‖∫z,f z ∂law‖≤Real.sqrt (∫z,‖Y z‖^2 ∂law)*ε)
    (Y:Z→ℂ)(y2:MemLp Y 2 law):
    let r:=2*m*width P.p D
    let E:=π ⁻¹' crowd P.p.threshold (neighbors r (o a)) m
    let H:=fun z=>if LongAt P.activities P.p (fun i=>A.K.hard t i (π z)) (o a) (2*m) D
      then filedRow A t s (π z) else 0
    let value:=fun z=>(τ:ℂ)*Y z*(δ z-Eᶜ.indicator H z)
    Integrable value law ∧ ‖∫z,value z ∂law‖≤
      Real.sqrt (∫z,‖Y z‖^2 ∂law)*(ε+M*Real.sqrt ((ballCost r).choose m:ℕ)*(x⁻¹)^q*κ^h):=by
  have gas (z:Z):P.activities.gas P.p (π z)≠0:=by
    intro zero
    have h:=(live z).ne'
    rw [Rep.eval,zero,mul_zero] at h
    exact h rfl
  have hx:0≤x:=zero_le_one.trans xp
  obtain ⟨integrated,bill⟩:=observed_long_entry law μ π πm original P.activities P.p
    (fun U i=>A.K.hard t i U) o (fun U i r=>(A.K.locality t i).carry U r)
    (fun U i=>A.K.charged t i U) (fun U i=>A.K.quiet t i U) gas
    w wp (filed_actor_stock A wp paid en t) s a b usedA usedB m D apart _ rare
    δ δm τ (M*x^d) ε tp (mul_nonneg mp (pow_nonneg hx _)) ep cap regular Y y2
  refine ⟨integrated,bill.trans (mul_le_mul_of_nonneg_left (add_le_add_right ?_ ε) (Real.sqrt_nonneg _))⟩
  exact divided_window_rate x κ M (M*x^d) xp kp k1 mp d q h m _ many le_rfl (o a)

end YM.Integration.FVA1Physical.Exchange.RoseCut
