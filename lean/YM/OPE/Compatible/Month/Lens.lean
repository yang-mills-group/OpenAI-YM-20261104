import YM.OPE.Compatible.Month.Up
/-!
 # Burner rate and secular width reserve.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma.Chase
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
variable (h:Chase A l)(X:∀ i, Support (A i).f) (hX:Lite A l (fun i=>( (X i).card:ℝ)))
include h
lemma dress : ∀ᶠ i in l, Geo.Width (A i).R.p (A i).R.clip P.top.width ∧ 2*(A i).R.p.supportExponent≤ (A i).R.p.B*(3*P.top.width/4):=by
   have hv:=h.port; let w:=P.top.width; have hw:0<w:=P.top.width_pos; let p:=P.top.supportExponent
   filter_upwards [hv,(tendsto_natCast_atTop_atTop.comp h.meter |>.atTop_mul_const hw).eventually_ge_atTop (4*(p+1))] with i hc hp
   have hs:=hc.budget; obtain ⟨hK,hB,hF,hE,hP,hQ⟩:=hs; change (barM A i:ℝ)*P.top.width≥_ at hp
   rw [hE,hP]; refine ⟨⟨hw,P.top.slow_selector, (div_le_iff₀ (show (0:ℝ)<(A i).R.p.B from by exact_mod_cast (A i).R.p.B_pos)).2 (by unfold p at hp; unfold barM at hp;linarith only [hp,hE])⟩,?_⟩; unfold barM p at hp; linarith [P.top.price_pos]
lemma emberLine : Wage A l (fun i=> (A i).R.beta) 1 :=by
   have hz:= h.high
   refine ((RateLE.const 2 (h.tense)).mul (h.run Rate.hat)).mono (le_of_eq (zero_add _))|>.transfer (?_)
   filter_upwards [h.port] with i hi; have hu:=hi.budget.2.2.2.2.2; rw [Real.norm_of_nonneg ((A i).cash.laws.intake.positive).le]; exact (hu.2: (A i).R.beta ≤ 2*βM A i).trans (Real.le_norm_self _)
lemma winds (ε:ℝ): Wage A l (fun i=> est (A i).R.p ε) 0 :=by
   unfold est; have hy:= h.billed.sound h; let D:=fate A; have hp:= (hy.add (RateLE.const 1 (h.tense)) h.tense); convert! ((RateLE.const 12 h.tense).mul hp|>.pow 4 h.tense).mul (RateLE.const (∑' i,Next.Scheduling.decay 4 ε i) h.tense) using 1; norm_num
include hX
lemma blares {p q θ:ℝ}{z:ι→ℝ} (hp:Wage A l z q)(hθ:0<θ)(a:ℝ): Wage A l (fun i=>burn (A i).R (X i) θ (z i) p 0 t (barM A i)) a:=by
   have he:Wage A l (fun i=> Real.exp ((A i).R.p.supportExponent*p - θ/2 * (barM A i))) (a-q) :=by
      have hh:=(h.track_pow (half_pos hθ) (a-q))
      apply RateLE.congr ( (show Wage A l (fun i=>Real.exp (P.top.supportExponent*p)*Real.exp (-(θ/2)*barM A i)) (a-q) by simpa only [zero_add] using (RateLE.const (Real.exp (P.top.supportExponent*p)) h.tense).mul hh))
      filter_upwards [h.port] with i hi
      rw [hi.budget.2.2.2.1,← Real.exp_add, sub_eq_add_neg,neg_mul]
   have hh:= (RateLE.const 2 h.tense).mul ((hX.sound h).mul ((h.winds t).mul (he.mul hp)))
   rw [sub_add_cancel] at hh; simpa only [burn,zero_mul,add_zero,zero_add] using hh
lemma revenues (ε : ℝ)(a : ℝ) : Wage A l (fun i=> marksV (A i).R (X i) P.top.width ε P.top.paths (loopBill G L (A i).x) (barM A i)) a:=by
    have hp:=P.top.width_pos; let C:=P.top.paths; let t:ℝ:= P.top.width
    have he (c:ℝ)(i:ℕ):=h.blares (p:=(1+(i:ℝ)*2)) (t:=ε) X hX (RateLE.const (2^i*C) h.tense) hp c
    have hh:=(h.blares (t:=ε) (p:=1+(2:ℕ)* (2:ℝ)) X hX (by convert! (RateLE.const ((2:ℝ)^(2:ℕ)) h.tense).mul (h.run (loopBill_rate G L)) using 0: Wage A l (fun i=>2^ (2:ℕ)*loopBill G L (A i).x) (0+0)) hp a)
    have hm: Wage A l (fun i=> (2*(A i).R.p.threshold)*lowerSize (A i).R.clip P.top.paths) 0 :=by
       apply RateLE.absBound (2*‖lowerSize P.top.clip P.top.paths‖) h.tense
       filter_upwards [h.port] with i hi; rw [hi.budget.2.2.2.2.1,norm_mul,Real.norm_of_nonneg (show 0≤2*(A i).R.p.threshold from mul_nonneg zero_le_two (A i).R.p.threshold_pos.le)]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); linarith only [(A i).R.p.threshold_le]
    have hv:=h.blares (t:=ε) (p:=Geo.lowCount) X hX hm (show 0 <3*P.top.width/4 by positivity) (a-1) -- edit
    have hS:=(hv.add (he (a-1) 3) h.tense).add (he (a-1) 4) h.tense
    unfold marksV; exact ((h.emberLine.norm.mul hS).mono (le_of_eq (by ring))).add hh h.tense
lemma attraction (ε:ℝ) :
 Wage A l (fun i=> marksV (A i).R (X i) (P.top.width) ε (P.top.paths) (loopBill G L (A i).x) (barM A i) + 2*((X i).card*(est (A i).R.p ε*incomingE G L (A i).x))) (-(11/10)):= (h.revenues X hX ε _).add (by
     simpa only [zero_add] using! (RateLE.const (2:ℝ) h.tense).mul ((hX.sound h).mul ((h.winds ε).mul (h.run (incomingE_rate G L))))) h.tense
end YM.PhysicalNext.Repeat.Aroma.Chase
