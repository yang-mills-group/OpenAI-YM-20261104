import YM.OPE.Compatible.Month.Chan
/-!
# Activation along chase
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard AnalyticBridge.VerifiedReset Geo
open Next.Rank.Thirst YM.OPE
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P:Teller G} {D:Patch} {E:ConnectedActivityE6.Target G P} {L:Side} {W a σ C κ v γ t s w:ℝ} {m:ℕ}
variable {o:ConnectedActivityE6.Target.Order G W}
variable {ι:Type*} {l:Filter ι} {A:ι→ Model D P L E o κ C m}
-- fix Lens environment.L
variable (D E L)
abbrev spillMass (i:ℕ)(x:ℝ):ℝ:= skimX G L x * echoL G L x^i -- G explicit
abbrev sheen (Q: ConnectedActivityE6.Target G P):= P.top.supportExponent-Q.ε
variable {D E L}
namespace Chase
variable (h:Chase A l)
include h
lemma terrainM (k:ℕ) (hp:∀ᶠ i in l, ‖(A i).g‖ ≤ spillMass (G:=G) L k (A i).x):∃ v:ℕ,∀ᶠ i in l,
 Sparta (A i).R (A i).V (A i).forest (A i).sheet.V (sheen E) (freight E L κ (A i).x) (incomingK G L (A i).x) (spillMass (G:=G) L v (A i).x) (Real.exp (-(echoM A i)^(2:ℕ))):=by
   obtain ⟨n,hx⟩:=operates D L E o C m h.1 h.2.1 h.2.2.1 h.2.2.2.1 k 2
   refine ⟨n,?_⟩; filter_upwards [h.port,h.select_height.eventually hx,hp] with i hi hs hv
   obtain ⟨a,b,c,hK⟩:=hi.walk
   exact hs a b c (A i).cash hi.height hi.stamp hi.Knows hK (A i).forest (A i).sheet hi.moment hi.weather hi.healthy (A i).g hi.chart hv
lemma tins (j:ℕ) :∀ᶠ i in l,4*spillMass (G:=G) L j (A i).x ≤ (A i).R.p.threshold:=by
   filter_upwards [h.port,h.high.eventually_gt_atTop 0,h.select_height.eventually (Delay.monitor_pays G L j (show (0:ℝ)≤4 by norm_num) (show (0:ℝ)<1 by norm_num))] with i hi hx h
   rw [Real.rpow_one] at h; rw [hi.budget.2.2.1]; unfold spillMass skimX; rw [Real.rpow_neg (show 0≤betaF G (A i).x L from hx.le),← Real.sqrt_eq_rpow]; rw [mul_left_comm]
   exact mul_le_mul_of_nonneg_left h (by positivity)
lemma pilots : ∃ n:ℕ,∀ j:ℕ, ∀ᶠ i in l,∀ q U, naked (A i).V q n U (spillMass (G:=G) L j (A i).x) → ordFrame (A i).V (halo 1 q) (U:Config G (A i).f) ∧ ordBest (A i).V q U:=by
   obtain ⟨r,n,hp,hx⟩:=helmet D P.bind h.1
   refine ⟨n,fun j=>?_⟩; have hv: Rate G L (-(1/2)) (spillMass (G:=G) L j):=by simpa only [zero_mul,add_zero] using! ((Rate.power (a:=-(1/2:ℝ))).mul (Rate.bill.pow j))
   filter_upwards [h.port,h.select_height.eventually (hv.below (by linarith) r hp)] with i hi he q U h
   exact hx (A i).V hi.height hi.port.2.2 _ _ fun x hX=> ((h x hX).trans (le_abs_self _)).trans he
lemma shadeL : Wage A l (fun i=> Shade (A i).R) 0:=by
   have hE := h.billed.sound h; unfold Shade; push_cast; convert! ((hE.add hE h.tense)|>.add (RateLE.const (1:ℝ) h.tense) h.tense).pow 4 h.tense using 1; norm_num
-- last threshold variables only after all Peña
lemma rosy {n:ℕ}(d:ι→ℕ)(hg:Lite A l (fun i=>(d i:ℝ)))(x:∀ i, Site (A i).c)(I:∀ i,Seats (A i).forest)(p:∀ i, Homer (A i) (x i) (d i) n (I i)) (k:ι→ℝ)(hk:Wage A l k 0) :
   let τ:=E.ε/2
   let v i:=marksV (A i).R (p i).X P.top.width τ P.top.paths (loopBill G L (A i).x) (barM A i)+2*((p i).X.card*(est (A i).R.p τ*incomingE G L (A i).x))
   (∀ᶠ i in l,Sable (A i).R (A i).V (p i).X (sheen E+τ) (cinnamon (A i).R (barM A i) (I i)) (v i) ∧ 4*Shade (A i).R*incomingK G L (A i).x≤τ ∧ v i≤1) ∧
    Wage A l (fun i=>promotion (A i).R (barM A i) (p i).X (incomingK G L (A i).x) (sheen E) τ (freight E L κ (A i).x) 0 (k i) (v i)) (-(11/10)):=by
       intro t v; obtain ⟨hX,hq,hK⟩:=dart h d hg x I p
       have ht:0<t:=half_pos E.usable; have hs:0≤ sheen E:= by unfold sheen; linarith [E.grants.1,E.usable]
       have hv: Wage A l v (-(11/10)):= attraction h (fun i=>(p i).X) hX t;let z(i):=incomingK G L (A i).x
       have he: 4*1=4:=by norm_num
       have hHI:=h.dress; have hZ := hv.tends (by norm_num) h.tense
       refine ⟨?_,?_⟩
       · have he:= (RateLE.const (4:ℝ) h.tense|>.mul h.shadeL)|>.mul (h.run (incomingK_rate G L (-1)))
         filter_upwards [h.port,hHI,hZ.eventually (ge_mem_nhds  (by norm_num:(0:ℝ)<1)),(he.tends (by norm_num) h.tense).eventually (ge_mem_nhds ht)] with i hi hv hX hy; refine ⟨?_,hy,hX⟩
         apply shelves hi.budget.1 hi.width hv.1 (crust (p i).good) _ ht (add_nonneg hs ht.le) hv.2
         rw [hi.budget.2.2.2.1]; unfold sheen t; linarith
       have hl: Wage A l (fun i=> Real.exp (v i)) 0:=RateLE.absBound 2 h.tense (by
         have he:= Real.continuous_exp.continuousAt.tendsto.comp hZ; rw [Real.exp_zero] at he
         filter_upwards [he.eventually (ge_mem_nhds (by norm_num:(1:ℝ)<2))] with i hi using (Real.norm_of_nonneg (Real.exp_pos _).le).trans_le hi)
       have hp:= (h.logK hq (sheen E+t) (-(11/10)))
       have hf := h.run (riseD E L h.2.2.2.1).1
       let w(i):= Real.exp ((sheen E + t)*coverNumber (barM A i) (p i).X)* (4*Shade (A i).R*z i/t)*freight E L κ (A i).x * Real.exp (v i)
       have hw: Wage A l w (-(11/10)):=by
          refine RateLE.congr (F:=fun i=>(Real.exp _ * _)*Shade (A i).R*(4 * t⁻¹)*freight E L κ (A i).x*Real.exp (v i)) (by simpa only [add_zero] using (((hp.mul h.shadeL).mul (RateLE.const _ h.tense)).mul hf|>.mul hl)) ?_
          filter_upwards with i; unfold w barM z; ring
       have hY:= ((hk.mul (RateLE.const 2 h.tense)).mul (((RateLE.const (2:ℝ) h.tense|>.mul hv)|>.mono (le_of_eq (zero_add _))).add hw h.tense)) -- type normalize
       simp only [zero_add] at hY; simpa only [promotion,mul_zero,zero_mul,add_zero,Wage,w,barM,z] using hY
end Chase
end YM.PhysicalNext.Repeat.Aroma
