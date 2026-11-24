import YM.PertExtension.CutoffFree
/-!
The position average is a **continuous** center average. Take the center patch made of the unit cells [0,1) added to all `origins` at the top (coordinates [P/8, P/4+ε], keeps clearance). Integrate endpoints immaterial. Sample exactly same shift on a sector (all slots). In finite profile sums use one lift of each relative torus site via `lift`; for all eventually admitted separated profiles support is in the near relative-position half-lengths.
The relative patch pose at o centered by u is ε(y-o)-εu. Can therefore use Mixed on swept profile. Corner-world notation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PositionX.Bare.Subcell
open MeasureTheory Set Function Filter PertExtension LatticePT Mixed CutoffFree
open scoped Topology BigOperators Classical
variable {n:ℕ} {I : Type*}
abbrev Space := Axis→ℝ
set_option maxHeartbeats 800000
def cube:Set Space:= Icc 0 1
lemma closedCube : IsCompact cube:= isCompact_Icc
lemma volumeOne : volume.real cube=1:= by rw [cube,measureReal_def, Real.volume_Icc_pi_toReal (by exact zero_le_one)];simp
def delta (n:ℕ)(u:Space):Points n:= points fun _=> WithLp.toLp 2 u
lemma continuousDelta : Continuous (delta n):= by
   unfold delta points; exact (PiLp.continuous_toLp _ _).comp (continuous_pi (fun _=> PiLp.continuous_toLp 2 _))

def sweep (f:Points n→ℝ)(ε:ℝ)(x:Points n):ℝ:= ∫ u in cube,f (x-ε • delta n u)
lemma sweep_ok (f:Points n→ℝ)(h:Continuous f): Continuous (fun z:ℝ × Points n=> sweep f z.1 z.2):= by
   apply continuous_parametric_integral_of_continuous (f:=fun (z:ℝ×Points n) u=> f (z.2-z.1 • delta n u)) (μ:=(volume:Measure Space)) _ closedCube
   exact h.comp (((continuous_snd (X:=ℝ)).comp continuous_fst).sub ((continuous_fst.comp continuous_fst).smul (continuousDelta.comp continuous_snd)))
lemma no_sweep (f:Points n→ℝ)(x): sweep f 0 x=f x:= by simp [sweep,volumeOne]

def valley (K:Set (Points n)) := (fun p:Points n × (ℝ × Space)=> p.1+p.2.1 • delta n p.2.2) '' (K ×ˢ (Icc 0 1 ×ˢ cube))
lemma includes (K:Set (Points n)) : K ⊆ valley K:= fun x hx=> ⟨(x,0,0), ⟨hx,⟨le_rfl, zero_le_one⟩,le_rfl,zero_le_one⟩, by simp⟩
lemma valley_compact {K:Set (Points n)}(h:IsCompact K) : IsCompact (valley K):=(h.prod (isCompact_Icc.prod closedCube)).image (continuous_fst.add ((continuous_fst.comp continuous_snd).smul (continuousDelta.comp (continuous_snd.comp continuous_snd))))
lemma valley_conf {K:Set (Points n)}(h:K⊆conf n): valley K⊆conf n:= by
   rintro x ⟨⟨w,r,y⟩,hw,rfl⟩ i j he; exact h hw.1 (add_right_cancel (b:=r • WithLp.toLp 2 y) he) -- add cancel b param?
lemma sweep_in {f:Points n→ℝ}{K:Set (Points n)}{x:Points n}{ε:ℝ}(h₁: ε∈Icc 0 1)(h:∀ x∉K,f x=0)(hx:x∉ valley K): sweep f ε x=0:= by
   unfold sweep; rw [MeasureTheory.setIntegral_congr_fun closedCube.measurableSet (g:=fun _=> (0:ℝ)) (fun u hu=> h _ (fun hb=>hx ⟨(x-ε • delta n u,ε,u),⟨hb,h₁,hu⟩,sub_add_cancel ..⟩)),MeasureTheory.integral_zero] -- lem check

variable {G : Gauge}(v: Fin n→ LatticePT.Word G) (q: ℕ+)(hq:1<q.val)
lemma small (k:ℕ): epsilon q k ≤ 1 := by unfold epsilon; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast (show 1≤ q.val from q.pos)) )
include hq
lemma sweep_limit {f:Points n→ℝ}(hf:Continuous f){K:Set (Points n)}(h:IsCompact K)(hK:K⊆conf n)(hx:∀ x∉K,f x=0): Tendsto (fun k:ℕ=> Mixed.polynomialTop v q k ((sweep f (epsilon q k)) ∘ points) 0) atTop (𝓝 (∫ x:Points n,realTyped v f x)):= by
   let w(t:ℕ):=sweep f (epsilon q t); simp_rw [all_energies]
   apply Grid.average_paths (hn:=fun k=>hasOrigin q k); intro u hu
   suffices H: Tendsto (fun i:ℕ=> kernel v q (w i) i (u i)) _ _ from H
   refine (Grid.integrable_spots (K:=valley K) (F:=fun t=>arrayAt v q (w t) t (u t)) hq ?_ (valley_compact h) (fun k x he=>?_ ) (fun k hk=>?_ )).2
   · intro s x he hs
     let g (i:ℕ):= Grid.sample q i (s i); have hh : Tendsto (fun i=>w i (g i)) atTop (𝓝 (f x)):= by
        nth_rw 1 [← no_sweep f x]; exact (sweep_ok f hf|>.continuousAt.tendsto (x:=(0,x))).comp ((show Tendsto (epsilon q) _ (𝓝 0) from (epsilon_zero hq).mono_right nhdsWithin_le_nhds).prodMk_nhds hs)
     exact hh.mul (ticket_limit v q hq u hu s (valley_conf hK he) hs)
   · rw [arrayAt, show w k (Grid.sample q k x)=0 from sweep_in ⟨(epsilon_pos q k).le,small q k⟩ hx he,zero_mul] -- zero_mul
   · rw [realTyped,hx _ (fun h=>hk (includes K h)),zero_mul]
end YM.PositionX.Bare.Subcell
