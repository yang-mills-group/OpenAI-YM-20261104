import YM.X.Dock.Port
/-!
# PD extension. Move ∆ like on expansion kernel, but not blind when read.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir.Dock
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset MeasureTheory Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Imprint CellsInt Beamer Asymptotics Crate.Fund
open Maxwell (Green normal grad)
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {m k d:ℕ} {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V] {n:Side} {q:ℕ+}{r R e c:ℝ} {A B:Scaff}{φ γ θ:E4→ℝ}
local notation "ε"=> epsilon q
local notation "L"=>(atTop:Filter ℕ)
variable (hq:1<q.val)(χ:Floor R){u v:Mist ℝ}
abbrev westOf (i:Axis)(u:Mist ℝ):Mist ℝ:=fun j z=>u j (z-step i)
abbrev prospect (l:Axis)(q:ℕ+)(u:Mist ℝ): Mist ℝ:= fun i z=> (epsilon q i)⁻¹ * (u i (z+step l)-u i z)
lemma prospect_eq (X Z:Fielding.Walk)(l:Axis)(A:Scaff): pin q X (run q Z (d+1) (ds l A))=prospect l q (pin q X (run q Z d A)):= by ext1 i; ext1 z; simp only [pin,run,prospect,sprite_val, ds_val, map_add,wrap_step,add_assoc,←mul_sub]; rw [show 2+(d+1)= (2+d)+1 by omega,pow_succ,mul_inv]; ring
lemma twice (i:Axis)(u v:Mist ℝ): westOf i (prospect i q (u*v))=westOf i u * westOf i (prospect i q v)+westOf i (prospect i q u)* v := by ext1 k; ext1 z; simp only [westOf,prospect,Pi.add_apply,Pi.mul_apply,sub_add_cancel]; ring
-- gradient to read.Focus only outer.Can move via Visa technical ease.
include hq
lemma west (he:0≤R)(hr:R<r)(i:Axis)(h:Focus q r 0 u φ):Focus q R 0 (westOf i u) φ:= by
    obtain ⟨C,hc,hV⟩:= h.bank.who; have hp (x:E4)(z:Fielding.Walk)(hz:plot q z x)(hx:x≠0)(he: ‖x‖≤R) : Tendsto (fun j=> westOf i u j (z j)) atTop (𝓝 (φ x)):= by
       let v(k:ℕ):=z k - step i; apply h.foot x v ?_ hx (he.trans hr.le); simpa only [sub_zero] using! (plot.sub hz (plot.constant hq (step i)))
    refine ⟨⟨⟨C,hc,?_⟩,fun x hx he z hz=>?_⟩,hp⟩; swap; · exact ⟨_, by simpa only [sub_zero,zpow_zero,one_smul] using! hp x z hz hx he⟩
    filter_upwards [hV,gate_shift hq _ _ hr he (-step i)] with j hj hu z hz; simpa only [westOf,price,zpow_zero,mul_one,sub_eq_add_neg] using! hj _ (hu z hz)
-- compact derivative
abbrev fcut (q:ℕ+)(s:ℕ→Lane)(k:ℕ): Lane:= ((epsilon q k)⁻¹) • s k
variable (i:Axis)
abbrev sideF (q:ℕ+)(χ:Floor R)(i:Axis):= fcut q (fun k=> changed (Floor.maskL q χ k) i)
lemma forwards (p:E4→ℝ)(h:ContDiff ℝ ∞ p)(x:E4)(Z:Fielding.Walk)(hz:plot q Z x): Tendsto (fun k=> prospect i q (fun j z=> p (spot (ε j) z)) k (Z k)) L (𝓝 (Maxwell.grad i p x)):= by
     choose Y hy hY using fun k:ℕ=> reach_exists [i] h (epsilon_pos q k) (spot (ε k) (Z k)); have he : Tendsto Y L (𝓝 x):= by
         apply hz.congr_dist (squeeze_zero (fun i=>dist_nonneg) (fun k=>hy k) ?_); simpa using! ((paths hq).cutoff.const_mul (1:ℝ))
     refine ((cMore h i).continuous.continuousAt.tendsto.comp he).congr fun k=>?_ ; apply Eq.symm; change (ε k)⁻¹* Interval.grads [i] (fun z=>p (spot (ε k) z)) (Z k)=_; rw [← steps_match,hY,List.length_cons,List.length_nil,Nat.zero_add,pow_one, inv_mul_cancel_left₀ (epsilon_pos q _|>.ne')]; rfl
lemma maskF_focus : Focus q R 0 (shutter (sideF q χ i)) (-(Maxwell.grad i χ.s)):= by
   let h:=Floor.changed_visa hq χ i; let v:= Visa.asPow (c:=(-1)) h; refine ⟨?_ ,fun x z hz hx he=>?_⟩
   · have H:(-1:ℤ)+1=0:= by norm_num
     change Visa q R 0 0 (fun j z=> sideF q χ i j z); simpa only [zpow_neg,zpow_one,H, sideF,fcut,Finsupp.smul_apply,shutter] using v -- applicative
   let w:Fielding.Walk:=z-(fun _=> step i); refine ((forwards hq i χ.s χ.s.contDiff x w (by simpa only [sub_zero] using plot.sub hz (plot.constant hq (step i)))).neg).congr (fun k=>?_);  change -prospect i q (fun j z=> χ.s (spot (ε j) z)) k (w k)=_; unfold sideF fcut shutter prospect; rw [Finsupp.smul_apply,changed_point]; change -( _* (χ.s (spot _ _)-_))=_; unfold w; simp only [Pi.sub_apply,sub_add_cancel,Floor.masking,smul_eq_mul];ring
lemma maskF_ship : Starboard q R (shutter (sideF q χ i)) := (χ.changed_ship hq i).mono (fun k hk z hz=> hk z (fun h=> hz (show shutter _ k z=0 from by unfold shutter sideF fcut; rw [Finsupp.smul_apply]; apply Eq.trans (congr_arg (_ • ·) h) (smul_zero _))))
omit hq in
lemma secure_grad (a:E4)(h:R<‖a‖): Maxwell.grad i χ.s a=0:= by
    have he: (χ.s:E4→ℝ) =ᶠ[𝓝 a] 0:= by
         filter_upwards [continuous_norm.continuousAt.tendsto (lt_mem_nhds h)] with x hx; apply χ.s.zero_of_le_dist; rw [dist_zero_right]; change R<‖x‖ at hx; linarith [χ.h,χ.s.rOut_pos]
    unfold Maxwell.grad Analysis.D; rw [he.fderiv_eq, fderiv_zero]; rfl -- name
lemma magnify_side (h:Focus q R (-3) u φ): Integrable (fun x=> -Maxwell.grad i χ.s x*φ x) ∧ Tendsto (divideW q (sideF q χ i) u) L (𝓝 (∫ x:E4, -Maxwell.grad i χ.s x*φ x)):= by
    refine Focus.zoomed hq (show Focus q R (-3) (shutter _*u) _ from (maskF_focus hq χ i).mix h) χ.positive.le (star_smul (f:=u) _ (maskF_ship hq χ i)) (Eventually.of_forall (posed _)) ?_; intro z hz; simp only [Pi.neg_apply]; rw [secure_grad χ i z hz,neg_zero,zero_mul]
omit hq
-- algebraic identity.
variable (f:ℕ→Lane)
lemma side_stream (f g:Mist ℝ)(v:ℕ→Lane): divideW q v (prospect i q f * g)= divideW q (fcut q (fun k=> changed (v k) i)) (f * westOf i g) - divideW q v (f * westOf i (prospect i q g)):= by
    ext1 k; unfold divideW influx fcut; rw [Pi.sub_apply, ← mul_sub]; congr 1; -- maybe rw applied too late
    let A:=v k; let B:=nudged (v k) (step i); let r:Cover→ℝ:= fun z=> f k z*g k (z-step i); change beadR A _= beadR ((ε k)⁻¹ • (B-A)) r- _; rw [show beadR ((ε k)⁻¹ • (B-A)) r=beadR (B-A) ((ε k)⁻¹ • r) from ?_]; swap; · let t:= (ε k)⁻¹; unfold beadR; rw [map_smul]; simp_rw [Finsupp.linearCombination_apply,Finsupp.sum,Finset.smul_sum]; exact Finset.sum_congr rfl fun z _=> smul_comm ..
    rw [show beadR (B-A) _= _ from map_sub (Finsupp.linearCombination ℝ ((ε k)⁻¹ • r)) B A]; change _= beadR (nudged A _) _- beadR A _- beadR A _; rw [sendB,← bead_sub,← bead_sub]; apply congr_arg; ext1 z; unfold r prospect westOf; simp only [Pi.mul_apply,Pi.sub_apply,Pi.smul_apply,add_sub_cancel_right,sub_add_cancel,smul_eq_mul];ring
include hq
lemma range_focus (hf:Focus q R (-3) u φ)(hv:Focus q R 0 (westOf i v) γ)(hp: Focus q R 0 (westOf i (prospect i q v)) θ):
   Integrable (fun x=> -Maxwell.grad i χ.s x*(φ x*γ x)) ∧ Integrable (fun x=>χ.s x*(φ x*θ x)) ∧ Tendsto (divideW q (Floor.maskL q χ) (prospect i q u* v)) L (𝓝 ((∫ x:E4, -Maxwell.grad i χ.s x*(φ x*γ x))-(∫ x:E4,χ.s x*(φ x*θ x)))):= by
   obtain ⟨he,ht⟩:= magnify_mask hq χ (hf.mix hp); obtain ⟨hh,h⟩:= magnify_side hq χ i (hf.mix hv); rw [side_stream]; exact ⟨hh,he,h.sub ht⟩
end YM.PositionX.Chir.Dock
