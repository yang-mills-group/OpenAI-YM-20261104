import YM.MSbar.Scale.Axes
/-! Prepare rollout numerator on the analytic disk. Powers of s can be managed uniformly to
first order even though arbitrarily many fields / labels are evaluated at a loop coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Scale.Flight
open Dim Symbol Function Set Filter Metric Complex MeasureTheory
open scoped Topology BigOperators Classical ContDiff
variable {f g:Vec}{a:ℂ}{n i:ℕ}
/-- Here supply numerator multipliers by Taylor degree. -/
def table (b:ℂ) : ℕ→(ℕ→ℂ)→ ℂ→Vec→Vec
    | 0,_,a,h=> b • past a h
    | n+1,L,a,h=> higher (table b n (fun n=>L (n+1)) (a-1) (strip h)) + fun _=>L 0*h 0
variable {b:ℂ}{L:ℕ→ℂ}(hf:Great f)(hg:Great g)(he:Land (a-n))
include hf hg he
lemma grouping : table b n L a (f+g) = table b n L a f + table b n L a g:=by
   induction n generalizing a L f g with
   | zero=> rw [table]; change b • rollout 0 _ _=_; rw [plus hf hg he];exact smul_add ..
   | succ n ih=> simp only [table,strip_plus hf hg,ih (strip_tame_ray hf) (strip_tame_ray hg) (slope_shift.mp he)]; funext t; simp [higher]; ring
omit hg
lemma multiplier (c:ℂ): table b n L a (c•f)=c • table b n L a f:=by
   induction n generalizing a L f with
   | zero=> rw [table]; change b • rollout 0 _ _=_; rw [scalar hf he]; exact smul_comm ..
   | succ n ih=>simp only [table,strip_scale hf,ih (strip_tame_ray hf) (slope_shift.mp he)]; funext x; simp [higher]; ring
omit hf in
lemma vacuum : table b n L a 0=0:= by simpa using multiplier (f:=0) (L:=L) (b:=b) (HasTemperateGrowth.const 0) he 0
omit hf he in
lemma stake (h:∀ i<n,L i=b/(a-i)): table b n L a f= b • rollout n a f:= by
    induction n generalizing a L f with
    | zero=> rfl
    | succ i ih=> rw [table,ih ?_]; swap
                  · intro j hj; rw [h _ (by omega), show a- (↑(j+1:ℕ):ℂ) = a - 1-j by push_cast; ring]
                  funext t; simp [rollout, higher,h]; ring
section
variable {X:Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {F:ℂ×(X×ℝ)→ℂ} {U:Set ℂ} (hu:IsOpen U) {r:ℂ→ℂ}(hr:DifferentiableOn ℂ r U)
omit hf he
include hu hr
lemma past_AH (hl:∀ z∈ U, Land (r z))(hF:AH U F): AH U (fun p:ℂ×(X×ℝ)=> past (r p.1) (fun t=>F (p.1,p.2.1,t)) p.2.2):=by
    let t:ℂ→ℂ:= fun z=> -r z-1; have ht:DifferentiableOn ℂ t U:= hr.neg.sub_const _
    let v(p:ℝ × ℂ):= weight (r p.2) p.1
    have hw : ContinuousOn v (Icc 0 1 ×ˢ U):= fun p h=> (((Complex.continuousAt_ofReal_cpow p.1 (t p.2) (Or.inl (desc (hl _ h.2)))).comp (f:=fun x:ℝ × ℂ=>(x.1,t x.2)) (continuousAt_fst.prodMk (((ht.analyticOnNhd hu) _ h.2).continuousAt.comp continuousAt_snd))).neg).continuousWithinAt
    have h(u:ℝ)(_ :u∈ Icc 0 1): DifferentiableOn ℂ (fun z=>v (u,z)) U:=by
       have hd(z:ℂ)(hz:z∈U): t z≠0:= fun h=> by have H:= desc (hl z hz); change 0<(t z).re at H; simp [h] at H
       intro z hz; exact (((ht.differentiableAt (hu.mem_nhds hz)).const_cpow (c:=(u:ℂ)) (Or.inr (hd z hz))).neg).differentiableWithinAt
    exact AH.cauchy_average hu (hF.arguments (show HasTemperateGrowth (fun p:(X×ℝ)×ℝ=>(p.1.1,p.2*p.1.2)) by fun_prop)) continuous_id isCompact_Icc hw h
lemma table_AH {b:ℂ→ℂ}(hb : DifferentiableOn ℂ b U){R:ℕ→ℂ→ℂ}(hl: ∀ i<n, DifferentiableOn ℂ (R i) U)
    (hX:∀ z∈U, Land (r z - n))(hF: AH U F): AH U (fun p:ℂ × (X×ℝ)=> table (b p.1) n (fun i=>R i p.1) (r p.1) (fun v=>F (p.1,p.2.1,v)) p.2.2):=by
   induction n generalizing r R F with
   | zero=> exact (AH.holomorphic hu hb).mul (past_AH hu hr (by simpa using hX) hF)
   | succ n ih=> have ht:= ih (r:=fun z=>r z-1) (hr.sub_const _) (R:=fun i=>R (i+1)) (fun i hi=> hl _ (by omega)) (fun z hz=>slope_shift.mp (hX z hz)) (hF.rad_strip hu)
                 have hh:AH U (fun p:ℂ×(X×ℝ)=> (p.2.2:ℂ)):= AH.param_tame (great_cast.comp tame_projR)
                 exact (hh.mul ht).add ((AH.holomorphic (X:=X×ℝ) hu (hl 0 (by omega))).mul (hF.arguments (show HasTemperateGrowth (fun p:X × ℝ=>(p.1,(0:ℝ))) by fun_prop)))
end
end YM.MSbar.Scale.Flight
