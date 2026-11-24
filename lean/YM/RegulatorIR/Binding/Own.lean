import YM.RegulatorIR.Binding.Ends

/-! Define the *independent* diagram readout at the stated top mesh t. Real
Jacobian & density from the top cost, with analytic scale and arbitrary top
observable. Need even sides. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Binding
open PertExtension Laplace Chart Lattice Geometry Geometry.Field Geometry.End Orb Gauge MeasureTheory Filter Function Set Metric Exterior Wilson RG Series Series.Radial Series.Tested Diagram.Formal Diagram Diagram.Gaussian Budget Budget.Packet Budget.Layer Budget.Tuple PowerSeries GaussianScore Tree Tree.Forest Step Ledger Ledger.Sky
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical PowerSeries
variable {G:Gauge}{f:Side}

def workStory (N:Scale)(A:Hook G Empty (OEdge f)): ℕ→ℝ:= tomorrow (apogee (startO N)) (tip A) 0
def storyPT (N:Scale)(A:Hook G Empty (OEdge f)): ℕ→ℝ:= Tested.divide (workStory N A) (workStory N (1:Hook G Empty (OEdge f)))
def plotPT (N:Scale)(A:Hook G Empty (OEdge f))(s:ℕ):ℕ→ℝ:= fun e=> storyPT N A (s+e)
lemma anchor (N:Scale) (hf:Even f.val): 0<workStory (G:=G) N (1:Hook G Empty (OEdge f)) 0:=by
 let X:=apogee (startO (f:=f) (G:=G) N);let P:= Chart.tangent G (Empty⊕Cotree f); let j:=morning G (Empty⊕ Cotree f)
 let g(x: Meadow G (Empty⊕Cotree f)):= normTerm (aura (tip (1:Hook G Empty (OEdge f)))) (priceMap X) 0 (x,1,0)
 have ht: P≠0:= NeZero.ne (Chart.tangent G (Empty⊕Cotree f))
 have h:Integrable g (Chart.tangent G (Empty⊕Cotree f)):= ((((start (G:=G) N hf).integrates (Last.carries hf)).allows (A:=tip (1:Hook G Empty (OEdge f))) (blade_c Empty shapeOne)).entry).protects _ 0 (1,0)
 have hp x :g x=j* Real.exp (-jet (priceMap X) 2 (x,1,0)):= by
    let Q: Angle (Empty⊕Cotree f) Empty G :=(x,1,0)
    have he: normTerm (aura (1:Hook G (Empty⊕Cotree f) Empty)) (priceMap X) 0 Q = _:= (coeff_mk ..).symm.trans (show (coeff 0 (PowerSeries.mk (fun i=>normTerm (aura (1:Hook G (Empty⊕Cotree f) Empty)) (priceMap X) i Q))) = _ from congr_arg (fun k: PowerSeries ℝ=> coeff 0 k) (prints (priceMap X) (aura 1) Q))
    change normTerm (aura (1:Hook G (Empty⊕Cotree f) Empty)) (priceMap X) 0 Q=j*Real.exp _
    rw [he,PowerSeries.coeff_C_mul,coeff_zero_eq_constantCoeff_apply,map_mul,← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,exp_start, inscription, PowerSeries.coeff_mk,jet_zero]
    change Real.exp _ * ((1*j)*1)=_; rw [one_mul,mul_one,mul_comm]
 have he x :0<g x := hp x |>.symm ▸ mul_pos (dawn ..) (Real.exp_pos _)
 apply (integral_pos_iff_support_of_nonneg (f:=g) (fun _=>(he _).le) h).mpr; rw [eq_univ_of_forall (s:=Function.support g) (fun i=>(he i).ne')]; exact Measure.measure_univ_pos.mpr ht

structure Plan (G:Gauge)(f:Side)(A:Hook G Empty (OEdge f)): Prop where
 law : Allowed G f (fun t u=> A t u 1)
 tune : Tune A
lemma top_truth (N:Scale)(A:Hook G Empty (OEdge f)) (he:Even f.val)(h:Plan G f A): Aspiration (goal N A) (storyPT N A):=by
 let F:Hook G Empty (OEdge f):= startO N
 have hu:= start N he (G:=G); have hh:= wind hu h.tune (allowed_top N A h.law) he; have hp := wind hu shapeOne (allowed_top N 1 (by intro k hk i t; rfl)) he
 intro i
 obtain ⟨c,hc,H⟩:= (hh.quotient hp (anchor N he).ne') i
 refine ⟨c,hc,?_⟩; filter_upwards [H,eventually_pos] with t ht hr
 convert ht using 1; simp only [Pi.sub_apply, goal, storyPT, workStory,Pi.div_apply];rw [mul_div_mul_left _ _ (by positivity)]
end YM.RegulatorIR.Binding
