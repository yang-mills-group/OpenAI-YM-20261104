import YM.FormalOPE.RG10.OpenSlots.Chip
/-!
 # current kernel ledger (formal). Two parameters Q (quadratic symmetric form, NOT
    necessarily positive full rank) and W (exponential weight relative to leading Hessian,
    with or without >formal higher Gaussian parameters, **WITHOUT Jacobian**).
    Bank these versus the genuine hierarchy. Need positivity only upon restricting to
    truss variables; next episode will assume internally (proved later from the ledger).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.OpenSlots
open MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open Inherit Push.Loops Chart Lattice RG GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open Papers Warp Line Roof Router
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {c f n: Side}
section
variable (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E]
structure Quadratic where
 P : E →ₗ[ℝ] Module.Dual ℝ E
 side : ∀ x y, P x y = P y x
variable {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F]{E}
namespace Quadratic
 def flourish (Q:Quadratic E)(x:E): ℝ:= Q.P x x
 def drag (d:F→ₗ[ℝ] E)(Q:Quadratic E): Quadratic F:= ⟨LinearMap.compl₂ (Q.P.comp d) d, fun x y=> Q.side (d x) (d y)⟩
 def addOn (U V: Quadratic E):Quadratic E:=⟨U.P+V.P, fun x y=> congr_arg₂ (· + ·) (U.side x y) (V.side x y)⟩
 def genesis (w:PowerSeries ℝ)(p:E→ℝ): Quadratic E:= ⟨term w 0 • MultiGauge.Splice.polar p, fun x y=> by simp [side_p,add_comm]⟩
lemma native (w:PowerSeries ℝ)(p:E→ℝ)(x:E): (genesis w p).flourish x=2*(term w 0*jet p 2 x):= by rw [← origin_p]; unfold flourish genesis; simp; ring
variable [FiniteDimensional ℝ E][FiniteDimensional ℝ F]
lemma payments (d:F→ₗ[ℝ] E)(w:PowerSeries ℝ)(p:E→ℝ)(h:ContDiffAt ℝ ω p 0)(x:F): (genesis w p).flourish (d x)=(genesis w (p ∘ d)).flourish x:= by
 rw [native,native,←read_rise,←read_rise,← Vault.climbing d (h.of_le le_top), caught] -- `h.of_le` syntax wrong
end Quadratic
end
variable {L:Fabric G n}(T:Cloth L) (J:ChartRatio G) (w:L.Cost→PowerSeries ℝ)
structure Unmasked (G:Gauge) (n:Side) where
 Q: Quadratic (Flats G n)
 W: Ticket (Flats G n)
 def initialFull (G: Gauge)(n:Side)(w:PowerSeries ℝ): Unmasked G n:= ⟨Quadratic.genesis w firstBill, chip w firstBill⟩
 def remainderQ (x:Field T.choose): ℝ:= ∑ i, (Quadratic.genesis (w i) (cost_core T (some i))).flourish x
 def remExponent : Ticket (Field T.choose):= ∏ i, chip (w i) (cost_core T (some i))
structure Bank (U:Unmasked G n) (Λ:Law (Field T.choose)) (V:Ticket (Field T.choose)): Prop where
 main x: Λ.P x x= U.Q.flourish (castAt T x) + remainderQ T w x
 price : V = boost (castAt T) U.W * tissue J T.choose.Bulk * remExponent T w

lemma readyI (U:Unmasked G n){H:LocalRatio J}{Λ:Law (Field T.choose)}{V:Ticket (Field T.choose)}(h:Bank T J w U Λ V)(up:incline U.W): incline V:= by
 rw [h.price]; apply pool (pool (preserve_boost _ up) (awake H))
 unfold incline remExponent; simp_rw [map_prod, show ∀ i : L.Cost, constantCoeff (chip (w i) (cost_core T (some i)))=1 from fun i=> restores ..]; simp
variable (a:L.Accounts→PowerSeries ℝ) (H:∀ i, 0<term (a i) 0)
-- first valuation all fields
include H in
lemma paidRoot : Bank T J (a ∘ some) (initialFull G n (a none)) (evidence (model L T.choose a).target (enough L T.choose a H).entire) (Stack.weight J (model L T.choose a)):= by
 let U:= model L T.choose a
 have he: cost_core T none=firstBill ∘ castAt T:= funext fun x=> by unfold firstBill; simp_rw [Function.comp_apply,accord_top]; rfl
 constructor
 · intro x; let V:=fun i=> U.field i ∘ expLinks G T.choose.Bulk
   change MultiGauge.Splice.polar (U.target ∘ expLinks G T.choose.Bulk) x x= _
   have hh p: (MultiGauge.Splice.polar p) x x = 2 * jet p 2 x:= by rw [← origin_p]; ring
   rw [hh, show U.target ∘ expLinks G T.choose.Bulk=∑ i,term (a i) 0 • V i from funext (fun x=> by rw [Finset.sum_apply]; rfl)]
   rw [jetSum (u:=fun i=>term (a i) 0) _ V (fun i=> ((enough L T.choose a H).sincere i).smooth), Finset.mul_sum]
   simp_rw [show ∀ i,2*(term (a i) 0 * jet (V i) 2 x)=(Quadratic.genesis (a i) (cost_core T i)).flourish x from fun i=> (Quadratic.native ..).symm]
   rw [Fintype.sum_option,he]; exact congr_arg₂ (· + ·) (Quadratic.payments (castAt T) _ _ firstGranted x).symm rfl
 rw [OpenSlots.weight (U:=model L T.choose a) (enough L T.choose a H)]
 change tissue J T.choose.Bulk * (∏ i:Option _, chip (a i) (cost_core T i))= (boost _ (chip (a none) _))*_ * _
 rw [Fintype.prod_option, he, ← pullPay (castAt T) _ firstBill firstGranted,← mul_assoc,mul_comm (tissue _ _)]; rfl
end YM.FormalOPE.RG10.OpenSlots
