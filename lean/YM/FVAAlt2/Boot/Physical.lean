import YM.FVAAlt2.Booth.Bank
import YM.Comparison.RG02.Bare.Signals
import YM.FVAAlt2.Rocket.Reading
/-!
# Physical (perturbative!) gadget input in Leg θ series. No integration R.price replaced. Projection to causal common cover Crew.Point after.Est. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Boot
open Function Set Filter Finset MeasureTheory Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Geometry Prim Diagram Diagram.Formal PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth
open Lattice RG Precision Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.FVAAlt2 Integral Wilson Exterior Arm
open FreeResolvent (flatten)
open PowerSeries
open scoped Topology BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {f:Side}{n p:ℕ}{G:Gauge} {W:Type}
local notation "X"=> fieldDir G f 1
-- pin orientation true periodic; faceValue uses path, exactly boot loop. No quotient projection. $
def pinto (P : Lattice.Face (Per f)): Lattice.Face ℤ:= ( Lattice.lift P.1, P.2 )
def weights (V:Lattice.Face ℤ→ Orders (Foot G)) (f:Side):Orders (Pin f G):= ∑ i:Lattice.Face (Per f), sendL (imprint G f) (V (pinto i))
variable (V:Lattice.Face ℤ→Orders (Foot G))
def rankC (B:Binding.Scale)(V:Lattice.Face ℤ→Orders (Foot G)) : Prop:= Prim.Plane B G V
variable (H:Binding.Scale)(h:Prim.Plane H G V)
lemma facade (t:Lattice.Face (Per f))(U:Config G f): faceValue (U ∘ around f) (pinto t)=faceValue U t:=by rw [ show U∘around f=expandAt 0 U by ext1 i; simp [expandAt,around],faceValue,travel_at,add_zero, show wrap f (pinto t).1=_ from wrap_lift t.1 ]; rfl
include h
lemma symbol_p : Vacuum (weights V f):= Booth.workOrder Finset.univ _ fun i _=> Booth.used _ ((h _).form le_rfl)
lemma symbol_k : gradedSymmetric (weights V f):= by
    intro i j; unfold weights; rw [Finset.sum_apply,Finset.sum_apply]; exact symmetric_sum fun k _=> Booth.known _ ( h (pinto k)|>.smooth) i j
lemma opening (x:X) (e:ℕ)(he:0<e): coeff e (flavor 2 (FreeResolvent.flatten x) (weights V f))= -coeff (e+2) (Prim.tale (fun t:ℝ=> H.beta t* Wilson.energy (sample t x))) :=by
    let F(i: Lattice.Face (Per f)):= flank (Prim.plain H G (pinto i)) (flatten x ∘ imprint G f)
    have H' i: ContDiffAt ℝ ∞ (F i) 0:= (Prim.boons G H _).some.smooth_v (flatten x ∘ imprint G f)
    have hx : ∑ i,F i=(fun t:ℝ=>H.beta t * Wilson.energy (sample t x)):= by
       ext1 t; rw [Wilson.energy, Finset.mul_sum,Finset.sum_apply]; refine sum_congr rfl fun i _=>?_ ; change H.beta t * G.price (faceValue (win G ((t • flatten x)∘ imprint G f)) (pinto i))=_; rw [Tape.panorama,facade]; rfl
    rw [weights, Booth.flavor_sum,map_sum, ←hx, Prim.tale_sum _ F (fun _ _=>H' _),map_sum,← Finset.sum_neg_distrib]; exact sum_congr rfl (fun t _=> (Booth.payRoot _ 2 le_rfl (h (pinto t)) e he _).trans (neg_one_mul _))

def dormant : UnitCost := ⟨fun _=>1,contDiffAt_const,rfl⟩
omit h
-- any export absolute.Constant
lemma dormant_l (r:ℕ): Ribbon.Align r Clocks.flat dormant :=by intro i hi; rw [show Ribbon.fees dormant=Clocks.flat.beta from ?_]; ext1 x;simp [Clocks.flat,dormant,Ribbon.fees]
open Halo Profiles Source Labels
structure Scout (n:ℕ) where
   body : Portrait G
   Vt : ∀ f:Side, Config G f→ℝ
   gear : Orders (Foot G)
   sight : BasisT n n body gear
   ranks : Cluster.Ranks n gear
   expose (f:Side) (U:Config G f) (t) : Vt f U= body t (U∘ around f)
   prepared (f:Side) : Assembly.GradeAt n (Bulk.projected fun _ x=> (↑(Vt f x):ℂ))
   rooted (f:Side) : Lattice.GaugeInvariant (Vt f)
   payment (f:Side): Continuous (Vt f)
variable (S:Scout (G:=G) n)
def view (f:Side) : Orders (Pin f G):= Booth.sendL (imprint G f) S.gear
lemma visits (x:X)(t:ℝ): S.Vt f (sample t x)= outing G S.body ( flatten x ∘ imprint G f ) t:= by
   rw [S.expose f _ t]; unfold outing sample; rw [ ←Tape.panorama x t ]; rfl -- need unfold sample
-- priced through all orders
lemma cadre (e:ℕ): Within (e+n) (view S f e):= Booth.within _ (S.ranks e)
lemma theoryM (x:X) : ContDiffAt ℝ ω (fun t:ℝ=> S.Vt f (sample t x)) 0:=by
   let Q:ℝ×X→ℂ:= Bulk.projected (fun _ x=> (↑(S.Vt f x):ℂ)); have hx: ContDiffAt ℝ ω Q 0:= (S.prepared f).smooth
   let a(t:ℝ):=((t,t • x):ℝ × X); have ha:a 0=0:= Prod.ext rfl (zero_smul ℝ x); exact Complex.reCLM.contDiff.contDiffAt.comp (f:=Q∘ a) _ (ContDiffAt.comp (f:=a) (g:=Q) _ (by rw [ha]; exact hx) ( contDiffAt_id.prodMk (contDiffAt_id.smul contDiffAt_const) ))
lemma vision (x:X)(e:ℕ) : coeff e (flavor n (flatten x) (view S f))= coeff (e+n) (Prim.tale (fun t:ℝ=> S.Vt f (sample t x))) :=by rw [ _root_.funext (visits S x), S.sight.pose, PowerSeries.coeff_X_pow_mul, flavor_lo, Halo.shelter,coeff_mk ]; exact Booth.finish (imprint G f) (S.gear e) (S.sight.canopy e) (e+n) _ -- supply

end YM.RegulatorIR.FVAAlt2.Boot
