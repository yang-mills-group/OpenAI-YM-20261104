import YM.FormalOPE.RG10.BlockGauge.Weather
/-!
 # Evaluating normalized Markov denominator in the diagram integral
 Before any scaling. Independent auxiliary kernel, no estimate. Auxiliary world
 parameter `w` multiplies prices; e.g. leading w=t⁻² on all levels, or later incorporate
 ratio. All independent orbit bonds. Not using this as analytic estimate tool on growing period.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.BlockGauge
open Filter Topology Function MeasureTheory PertExtension PertExtension.Orb Lattice RG
open InversionWard Push.Loops
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c f n:Side}
namespace Fabric
variable (L : Fabric G n)
 def production (w:L.Cost→ℝ)(e:L.Clouds): ℝ:= ∑ i,w i * L.air e i
 def thermostat {n} (L:Fabric G n)(w:L.Cost→ℝ): ℝ:= match L with
 | .endcap _ _=>1
 | .layer S _ _ _ L=> zone (w none) _ _ G S * L.thermostat (fun i=> w (some i))
lemma thermostat_pos {n}(L:Fabric G n)(w :L.Cost→ℝ):0<L.thermostat w:= by
 cases L with
 | endcap=> exact zero_lt_one
 | @layer c f S H t hf L=> exact mul_pos (zone_pos S (w none)) (thermostat_pos L _)
termination_by structural L
@[fun_prop] lemma prod_cont (w:L.Cost→ℝ): Continuous (L.production w):= by unfold production; exact continuous_finsetSum _ fun i _=> continuous_const.mul (L.areal i)
@[fun_prop] lemma airlock (w:L.Cost→ℝ): Integrable (fun e=> Real.exp (-L.production w e)) L.later:= by
 let f (e):= Real.exp (-L.production w e)
 exact (show Continuous f from Real.continuous_exp.comp (prod_cont L w).neg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
variable (S:StepData c f)(B:S.patch.Branches S.kernel G)(t:S.Choices)(hf:_root_.Even f.val)(U: Fabric G c)
local notation "Γ"=> layer S B t hf U
lemma sectional (w:(Γ).Cost→ℝ)(e:U.LinksOn): (Γ).production w e = w none * (distance S (U.principal e)) + U.production (w ∘ some) (U.runoff e):= by
 unfold production; change ((∑ a:Option U.Cost,_)=_); rw [Fintype.sum_option]; rfl
lemma gone_zero (h:_root_.Even n.val)(w:(Fabric.endcap (G:=G) n h).Cost→ℝ)(e): (Fabric.endcap (G:=G) n h).production w e=0:= by unfold production; change ∑ i:Empty,_ =_; simp
lemma fullClosure {n:Side}(L:Fabric G n)(w:L.Cost→ℝ):
 (∫ e, Real.exp (-L.production w e) ∂L.later) = L.thermostat w := by
 cases L with
 | endcap => simp [gone_zero,thermostat]
 | @layer c f S B t hf U =>
    change (Option U.Cost→ℝ) at w
    let D:=layer S B t hf U
    let W:U.LinksOn→ℝ:= fun e=> Real.exp (- D.production w e)
    change (∫ e, W e ∂ U.always) = _
    have hp a (e:U.Clouds): W (U.combine a e) = heat S (w none) a * Real.exp (- U.production (w ∘ some) e):= by unfold W D; rw [sectional,principal_comb,runoff_comb,neg_add,Real.exp_add]; simp [heat]; rfl
    rw [← U.spread_packs.integral_comp' W, show (fun x=> W (U.spread.symm x))= (fun x=> heat S (w none) x.1 * Real.exp (- U.production (w ∘ some) x.2)) from funext (fun ⟨a,e⟩=> hp a e), integral_prod_mul (heat S (w none)) (fun x=> Real.exp (- U.production (w ∘ some) x)), fullClosure U]
    rw [now,mass]; rfl
termination_by structural L

lemma recorded (w:L.Cost→ℝ)(u:LinkFrame G n)(y:L.Clouds): L.installment w (L.combine u y) = L.production w (L.dry u y):= Finset.sum_congr rfl (fun a _=> congr_arg (w a * ·) (L.costs a u y))
-- exact normalization for all real weights. make reconstruct with genuine conditional choice germ.
lemma installmentClosure (w:L.Cost→ℝ)(u:LinkFrame G n):
 (∫ y, Real.exp (-L.installment w (L.combine u y)) ∂L.later) = L.thermostat w := by
 simp_rw [recorded]; exact ((L.mist u).integral_comp' (fun e=>Real.exp (- L.production w e))).trans (L.fullClosure w)
 def bright (w:L.Cost→ℝ)(u:L.LinksOn): ℝ:= Real.exp (-L.installment w u) / L.thermostat w
lemma normalized_assembly (w:L.Cost→ℝ)(u:LinkFrame G n): (∫ y,L.bright w (L.combine u y) ∂L.later)=1 := by
 unfold bright; rw [integral_div,installmentClosure,div_self (thermostat_pos ..|>.ne')]
-- every step normalization before ratio exactly:
lemma every (w:(Γ).Cost→ℝ)(u:(Γ).LinksOn):
 (Γ).bright w u=noise S t ((Γ).principal u) (U.principal (future S B t hf U u)) (w none) * U.bright (w ∘ some) (future S B t hf U u):= by
 unfold bright; rw [tax_split,neg_add,Real.exp_add]; unfold noise; simp only [neg_mul]; rw [show thermostat _ w=zone (w none) c f G S * U.thermostat (w ∘ some) from rfl]; rw [←div_mul_div_comm]; ring
end Fabric
end YM.FormalOPE.RG10.BlockGauge
