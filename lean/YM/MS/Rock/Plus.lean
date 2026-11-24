import YM.MS.Rock.Packet
/-!
# Bilinear energy at fixed complex dimension

Not contour prescription via PV. use proper on supporting subspaces. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Path Landau Arts Pilot Spin Arc Wire
open Metric
open scoped Topology ContDiff
variable {G:Gauge}{b c: Bool}{F H:Mob G}{U V:Rip G}
variable {E F: Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
  [NormedAddCommGroup F][NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {u v:Tree E ℂ}
omit [FiniteDimensional ℝ E] in lemma d_add (h: ContDiff ℝ ∞ u)(he: ContDiff ℝ ∞ v): Arc.d (u+v)=Arc.d u +Arc.d v:=funext fun p=> by unfold Arc.d; rw [fderiv_add (h.differentiable (by simp) _) (he.differentiable (by simp) _)]; rfl
omit [FiniteDimensional ℝ E] in lemma croll (h:ContDiff ℝ ∞ u)(he: ContDiff ℝ ∞ v)(n:ℕ) : pruning n (u+v)=pruning n u+pruning n v:=by
    induction n generalizing u v with
    | zero=>rfl
    | succ n ih=>
        have H : chop (u+v)=chop u+chop v:= by
             funext l; unfold chop; rw [d_add h he, d_add (fresh h) (fresh he)]; simp_rw [Pi.add_apply]; exact intervalIntegral.integral_add (((fresh (fresh h)).continuous.comp (show Continuous (fun x:ℝ=> (x*l.1,l.2)) by fun_prop)).intervalIntegrable 0 1) (((fresh (fresh he)).continuous.comp (show Continuous (fun x:ℝ=> (x*l.1,l.2)) by fun_prop)).intervalIntegrable 0 1)
        change pruning n _= pruning n (chop u)+ pruning n (chop v); rw [H]; exact ih (c_chop h) (c_chop he)
omit [FiniteDimensional ℝ E] in
lemma coill (h:ContDiff ℝ ∞ u)(s:ℂ)(n:ℕ): pruning n (s • u)=s • pruning n u:= by
    induction n generalizing u with
    | zero=>rfl
    | succ n ih=>
      have hz{u:Tree E ℂ}(h:ContDiff ℝ ∞ u): Arc.d (s • u)=s • Arc.d u:= funext fun p=> by unfold Arc.d; rw [fderiv_const_smul (h.differentiable (by simp) _)]; rfl
      have hu : chop (s • u)=s • chop u:= by ext; simp_rw [chop,hz h,hz (fresh h),Pi.smul_apply, intervalIntegral.integral_smul]; rfl
      change pruning n _= _; rw [hu]; exact ih (c_chop h)

omit [FiniteDimensional ℝ E] in
lemma meets (h:Ultra u){v:ℂ}(hw:v∈Town)(x:E): Integrable (fun r=> fetchP (cloud v) u r x) μhalf:= by
    obtain ⟨b,hb⟩:= exists_nat_ge (2*v.re+1); exact (shade_major h (shade_cloud (Z:=fun _:Unit=>v) (fun _=>hw) (fun _=>hb)) ()).values x
omit [FiniteDimensional ℝ E] in lemma core_pl (h:Ultra u)(hp:Reflect u)(he:Ultra v)(hk:Reflect v){z:ℂ}(hz:z∈Town) (n:ℕ): coreC (cloud z) n (u+v)=coreC (cloud z) n u+coreC (cloud z) n v:= by
   funext l; unfold coreC; rw [croll (h.smooth ()) (he.smooth ())]; simp only [fetching,fetchP,Pi.add_apply,Pi.smul_apply, smul_add]; rw [integral_add, smul_add]; exact meets ((pruned h (fun _=>hp) _).1) hz l; exact meets ((pruned he (fun _=>hk) _).1) hz l -- goal order
omit [FiniteDimensional ℝ E] in lemma core_m (h:Ultra u)(s:ℂ)(z:ℂ)(n:ℕ): coreC (cloud z) n (s • u)=s • coreC (cloud z) n u:= by
   funext p; unfold coreC; rw [coill (h.smooth ())]; simp only [fetching,fetchP,Pi.smul_apply]; rw [smul_comm s]; simp_rw [show ∀ a v:ℂ,a • s • v=s • a • v from fun _ _=>smul_comm .., integral_smul]
end YM.MS.Rock
