import YM.Integration.WilsonMaxwellThermometerLowerFiledGram

/-! Uniform lower-field price at a small reflected detector. The same
neighborhood works for every occupied coordinate and both chiral readings. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerLowerGramPrice
open Filter Set Finset Lattice Wilson Maxwell Maxwell.Free XSpace XSpace.Cirrus
open WilsonMaxwellThermometerLowerPointGram WilsonMaxwellThermometerLowerFiledGram
open scoped Topology BigOperators Classical
variable {G:Gauge}(a:Axis)(x:E4)

instance dim : FiniteDimensional ℂ (occupied G a x) :=
  FiniteDimensional.span_of_finite ℂ (finite_range _)

abbrev Index (G:Gauge)(a:Axis)(x:E4):=Fin (Module.finrank ℂ (occupied G a x))
private abbrev basis:=Module.finBasis ℂ (occupied G a x)

def token (z:occupied G a x):Index G a x→ℂ:=(basis a x).equivFun z

def reassemble (k:Index G a x→Bool→ℂ)(z:occupied G a x)(s:Bool):ℂ:=
  ∑i,token a x z i*k i s

def entry (i:Index G a x)(s:Bool):ℂ:=(panel G a x (basis a x i)) s

theorem trueRow (z:occupied G a x):reassemble a x (entry a x) z=panel G a x z:=by
  funext s
  calc
    _ = (panel G a x (∑i,token a x z i • basis a x i)) s:=by
      simp [reassemble,entry,map_sum]
    _ = _:=congrArg (fun v=>(panel G a x v) s) ((basis a x).sum_repr z)

private theorem perturb (k:Index G a x→Bool→ℂ){δ:ℝ}(pos:0≤δ)
    (fee:∀i s,‖entry a x i s-k i s‖≤δ)(z:occupied G a x):
    ‖panel G a x z-reassemble a x k z‖≤Fintype.card (Index G a x)*(δ*‖token a x z‖):=by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun s=>?_
  rw [←trueRow]
  change ‖(∑i,token a x z i*entry a x i s)-∑i,token a x z i*k i s‖≤_
  rw [←Finset.sum_sub_distrib]
  simp_rw [←mul_sub]
  calc
    _ ≤ ∑i,‖token a x z i*(entry a x i s-k i s)‖:=norm_sum_le .. 
    _ ≤ ∑_i:Index G a x,δ*‖token a x z‖:=by
      apply sum_le_sum
      intro i _
      rw [norm_mul,mul_comm]
      exact mul_le_mul (fee i s) (norm_le_pi_norm (token a x z) i) (norm_nonneg _) pos
    _ = _:=by simp

theorem continuousPrice (hx:0<x a):
    ∃C δ:ℝ,0<C ∧ 0<δ ∧ ∀ k:Index G a x→Bool→ℂ,
      (∀i s,‖entry a x i s-k i s‖≤δ) → ∀z:occupied G a x,
      ‖token a x z‖≤C*‖reassemble a x k z‖:=by
  obtain ⟨c,hc,cash⟩:=WilsonMaxwellThermometerLowerPointGram.original a x hx
    (basis (G:=G) a x).equivFun.toLinearMap
  let b:=max 1 c
  let n:ℝ:=Fintype.card (Index G a x)
  have hb:0<b:=zero_lt_one.trans_le (le_max_left ..)
  have hn:0≤n:=Nat.cast_nonneg _
  let δ:ℝ:=(2*b*(n+1))⁻¹
  have hδ:0<δ:=inv_pos.mpr (mul_pos (mul_pos (by norm_num) hb) (by linarith))
  refine ⟨2*b,δ,by positivity,hδ,?_⟩
  intro k hk z
  have cap:=cash z
  change ‖token a x z‖≤c*‖fun s=>read a x s z.val‖ at cap
  rw [←show panel G a x z=fun s=>read a x s z.val from funext (reported a x z)] at cap
  have cap':‖token a x z‖≤b*‖panel G a x z‖:=
    cap.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _))
  have split:‖panel G a x z‖≤‖panel G a x z-reassemble a x k z‖+‖reassemble a x k z‖:=by
    simpa using norm_sub_le (panel G a x z-reassemble a x k z) (-reassemble a x k z)
  have paid:‖token a x z‖≤b*(n*(δ*‖token a x z‖)+‖reassemble a x k z‖):=
    cap'.trans (mul_le_mul_of_nonneg_left (split.trans (add_le_add
      (perturb a x k hδ.le hk z) (le_rfl))) hb.le)
  have half:b*n*δ≤1/2:=by
    change b*n*(2*b*(n+1))⁻¹≤1/2
    rw [←div_eq_mul_inv,div_le_iff₀ (by positivity : 0<2*b*(n+1))]
    linarith
  have term:=mul_le_mul_of_nonneg_right half (norm_nonneg (token a x z))
  nlinarith

def finiteEntries (W:Initialize G)(V:Normalize.Store G)(t:Sample 2)(i:Index G a x)(s:Bool):ℂ:=
  sample a x W V s (basis a x i) t

/-- Numerical entries of the genuine normalized public program are issued
at every nearby eligible auxiliary cell before any lower vector is chosen. -/
theorem original (W:Initialize G)(V:Normalize.Store G)(hx:0<x a):
    ∃C δ r:ℝ,0<C ∧ 0<δ ∧ 0<r ∧
      (∀ᶠ M in Front,∀u:pack 2,∀c∈M.Box,dist (M.rel u c) (center a x)<r →
        ∀i s,‖entry a x i s-finiteEntries a x W V ⟨M,u,c⟩ i s‖≤δ) ∧
      ∀k:Index G a x→Bool→ℂ,(∀i s,‖entry a x i s-k i s‖≤δ) →
        ∀z:occupied G a x,‖token a x z‖≤C*‖reassemble a x k z‖:=by
  obtain ⟨C,δ,hC,hδ,price⟩:=continuousPrice (G:=G) a x hx
  have H:∀ᶠ t:Sample 2 in Gate (center a x),∀i s,
      ‖entry a x i s-finiteEntries a x W V t i s‖≤δ:=by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro s
    have h:=WilsonMaxwellThermometerLowerFiledGram.original a x W V hx s (basis a x i)
    filter_upwards [Metric.tendsto_nhds.mp h δ hδ] with t near
    rw [←dist_eq_norm,dist_comm]
    exact near.le
  obtain ⟨r,hr,cert⟩:=gate_senses (center a x) H
  exact ⟨C,δ,r,hC,hδ,hr,cert,price⟩

end YM.Integration.WilsonMaxwellThermometerLowerGramPrice
