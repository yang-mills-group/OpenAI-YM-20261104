import YM.OPE.Compatible.Month.Burr
/-! # F-domain powered and exponent registers. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open AnalyticBridge.VerifiedReset
open Next.Rank.Thirst YM.OPE
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P:Teller G} {D:Patch} {E:ConnectedActivityE6.Target G P} {L:Side} {W a σ C κ v γ t s w:ℝ} {m:ℕ}
variable {o:ConnectedActivityE6.Target.Order G W}
variable {ι:Type*} {l:Filter ι} {A:ι→ Model D P L E o κ C m}
namespace Lite
variable {F K:Type*}[SeminormedAddCommGroup F][SeminormedAddCommGroup K]
variable {u v:ι→F}
theorem add (h:Lite A l u)(hv:Lite A l v)(ht:Chase A l): Lite A l (fun i=>u i+v i):=by
   obtain ⟨k,hk⟩:=h; obtain ⟨j,hj⟩:=hv; refine ⟨k+j+1,?_⟩; filter_upwards [hk,hj,ht.echoes.eventually_ge_atTop 2] with i hi h hb
   let p:=echoM A i; have he:1 ≤ p:=Delay.bill_ge ..; apply (norm_add_le _ _).trans
   have hx : k ≤ k+j:=Nat.le_add_right ..; have hy:j≤k+j:=Nat.le_add_left ..
   refine ((add_le_add hi h).trans (add_le_add (pow_le_pow_right₀ he hx) (pow_le_pow_right₀ he hy))).trans ?_
   rw [pow_succ,← mul_two]; exact mul_le_mul_of_nonneg_left hb (pow_nonneg (by linarith) _)
theorem ofLe {v:ι→K} (h:Lite A l u)(ht:∀ᶠ i in l,‖v i‖≤ ‖u i‖): Lite A l v:=by obtain ⟨d,h⟩:=h; exact ⟨d,(ht.and h).mono fun i hi=> hi.1.trans hi.2⟩
theorem shift (h:Lite A l u)(ht:u =ᶠ[l] v):Lite A l v:= h.ofLe (ht.mono fun i hi=>by rw [hi])
theorem flatC (v:F)(h:Chase A l): Lite A l (fun _=> v):=⟨1, (h.echoes.eventually_ge_atTop ‖v‖).mono fun _ he=> by simpa using he⟩
omit [SeminormedAddCommGroup F] in
theorem rmul {u v:ι→ℝ} (h : Lite A l u)(hp:Lite A l v):Lite A l (fun i=>u i*v i):=by
    obtain ⟨a,ha⟩:=h;obtain ⟨b,hb⟩:=hp; refine ⟨a+b,?_⟩;filter_upwards [ha,hb] with i hi hk; rw [norm_mul,pow_add]; exact mul_le_mul hi hk (norm_nonneg _) ((norm_nonneg _).trans hi)
theorem product_pw {u:ι→ℝ}(h:Lite A l u)(ht:Chase A l)(m:ℕ):Lite A l (fun i=>u i^m):=by induction m<;> first| simpa using Lite.flatC (1:ℝ) ht| next m ih=> simpa only [pow_succ] using! ih.rmul h
-- notation constants auto μ0. scale echo monotone any pay
lemma sound (h:Lite A l u)(hh: Chase A l): Wage A l u 0:=by
   obtain ⟨p,hp⟩:=h; exact RateLE.of_norm_le (by simpa only [mul_zero] using (hh.run (Rate.bill)).pow p hh.tense) hp
end Lite
namespace Chase
variable (h: Chase A l)
include h
def barM (A:ι→Model D P L E o κ C m) (i:ι):=(A i).R.p.B
lemma bora : barM A =ᶠ[l] fun i=> radiusB (βM A i):= h.port.mono fun _ hi=> hi.budget.2.1
lemma meter : Tendsto (barM A) l atTop:= (Work.E01.radiusB_tendsto.comp h.high).congr' h.bora.symm
lemma billed : Lite A l (fun i=>(barM A i:ℝ)):=by
   refine ⟨3,?_⟩; filter_upwards [h.bora,h.echoes.eventually_ge_atTop 3] with i hi ht
   have he : (barM A i:ℝ)<Real.log (βM A i)^2+1:=by rw [hi]; exact Nat.ceil_lt_add_one (by positivity)
   rw [Real.norm_of_nonneg (by positivity:(0:ℝ)≤barM A i)]; let v:=echoM A i; have hp : 3≤v:=ht; change _≤v^3; apply he.le.trans; suffices hu:v≤v^3 from le_trans (by unfold v echoM Delay.bill βM; have := Nat.cast_nonneg (α:=ℝ) (radiusB (A i).x); linarith) hu; exact le_self_pow₀ (by linarith) (by decide)
lemma track_pow {α:ℝ} (hα : 0<α): ∀ z:ℝ, Wage A l (fun i=>Real.exp (-α*barM A i)) z:=by
    intro z
    -- B(fine) ; cheaper than till α/2 eventually.
    apply RateLE.transfer (F:=fun i=> Real.exp (-(α/2)* Pressure.Stores.till (A i).x)) (h.run (Rate.cutoff (half_pos hα)))
    have hg : ∀ᶠ i in l, Pressure.Stores.till (A i).x ≤ 2*barM A i:=by
       let k:=G.slopeConstant*Real.log (L.val:ℝ); have he:(fun x=>x+k)=fun (v:ℝ)=> betaF G v L:=rfl
       have hm' (i): (A i).x= βM A i+(-k) := by unfold βM betaF k; ring
       filter_upwards [h.bora,h.high.eventually (Stock.stepsize (-k))] with i hi hk; change radiusB (βM A i+(-k))^2 ≤ _ at hk; rw [← hm'] at hk
       apply le_trans (b:=radiusB (A i).x) (by unfold Pressure.Stores.till; omega) _; rw [hi]; change _ ≤ 2*radiusB (βM A i)^2 at hk; nlinarith
    filter_upwards [hg] with i hi; rw [Real.norm_of_nonneg (Real.exp_nonneg _),Real.norm_of_nonneg (Real.exp_nonneg _)]; apply Real.exp_monotone; have h:=mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ).2 hi) hα.le;push_cast at h; linarith only [h]
lemma logK {u:ι→ℝ} (he:Lite A l u) (b:ℝ) : ∀ t:ℝ, Wage A l (fun i=> Real.exp (b*u i)* incomingK G L (A i).x) t:=by
    obtain ⟨j,hU⟩:=Lite.rmul (Lite.flatC b h) he; intro t; apply RateLE.transfer (F:=fun i=> Real.exp (-(1/2)*(Delay.fineMonitor G L (A i).x)^((1:ℝ)/5))) (h.run (Rate.monitor_cutoff (by norm_num) (by norm_num)))
    filter_upwards [hU,h.select_height.eventually (Delay.monitor_pays G L j (by norm_num:(0:ℝ)≤2) (by norm_num:(0:ℝ)< 1/5))] with i hx he
    unfold incomingK; rw [← Real.exp_add,Real.norm_of_nonneg (Real.exp_nonneg _),Real.norm_of_nonneg (Real.exp_nonneg _)]; apply Real.exp_monotone; linarith only [he,(Real.le_norm_self _).trans (show ‖b*u i‖ ≤ Delay.bill G L (A i).x ^ j from hx)]
lemma woe : ∀ t:ℝ, Wage A l (fun i=> Real.exp (-(echoM A i)^(2:ℕ))) t:=by
   intro t p hp
   filter_upwards [h.tense.eventually_ge_atTop 1, h.echoes.eventually_ge_atTop (-p)] with i hi hx
   rw [Real.norm_of_nonneg (Real.exp_nonneg _)]; apply Real.exp_monotone
   have hu:fate A i ≤ echoM A i:=by unfold fate βM at *; unfold echoM Delay.bill; have := Nat.cast_nonneg (α:=ℝ) (radiusB (A i).x); nlinarith
   nlinarith only [hu,hx,hi,mul_le_mul_of_nonneg_right hu (zero_le_one.trans (hi.trans hu)), mul_le_mul_of_nonneg_right hx (zero_le_one.trans hi)]
end Chase
end YM.PhysicalNext.Repeat.Aroma
