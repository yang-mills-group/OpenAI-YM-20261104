import YM.UVExt.FiscalLimit

/-! Exact equality on gauge orbit under the actual path functions. Tangent replacement uses it only after matching lower jets on the whole tensor space, not as independence of fine gauge increments. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function RG Precision Wilson Lattice Bid Exterior Laurent Filter Set Matrix
open Work.F04
open scoped Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {n : Side}

def tilt (u : Site n→G.Color) : Dir G n := fun p=> u p.1-u (p.1+step (axisEquiv.symm p.2))
def spunt (u : Site n→G.Color) (v : Dir G n) (t : ℝ) := Lattice.gauge (fun i=> G.lieExp (t • u i)) (represent (t • v))
def radLog (u : Site n→G.Color) (v : Dir G n) : ℝ→Dir G n := fun t i=> G.plog (G.mat (spunt u v t (i.1,axisEquiv.symm i.2)))
lemma spunt_zero (u : Site n→G.Color) (v : Dir G n) : spunt u v 0=1 := by funext e; simp [spunt,Lattice.gauge,link_one]
lemma spunt_read (u : Site n→G.Color) (v : Dir G n) (t : ℝ) p :
    spunt u v t p=G.lieExp (t • u p.1) * G.lieExp (t • v (p.1, coord p.2)) * G.lieExp (t • -(u (p.1+step p.2))) := by unfold spunt Lattice.gauge; rw [Work.F03.represent_link]; rw [smul_neg,Work.F03.exp_neg_color]; rfl
lemma spunt_smooth (u : Site n→G.Color) (v : Dir G n) e : ContDiff ℝ ω (fun i=> G.mat (spunt u v i e)) := by
   simp_rw [spunt_read,G.mat_mul]
   exact ((G.exp_jet.comp (contDiff_id.smul contDiff_const)).mul (G.exp_jet.comp (contDiff_id.smul contDiff_const))).mul (G.exp_jet.comp (contDiff_id.smul contDiff_const))
lemma radSmooth (u : Site n→G.Color) (v : Dir G n) : ContDiffAt ℝ ω (radLog u v) 0 := contDiffAt_pi.mpr fun i=> ContDiffAt.comp (f:=fun t=>G.mat (spunt u v t (i.1,axisEquiv.symm i.2))) _ ((by rw [spunt_zero]; change ContDiffAt ℝ ω G.plog (G.mat 1); rw [G.mat_one]; exact G.plog_diff)) (spunt_smooth ..).contDiffAt
lemma rad_zero (u : Site n→G.Color) (v : Dir G n) : radLog u v 0=0 := by ext i j; change radLog u v 0 i j=_; unfold radLog; rw [spunt_zero]; simp
lemma rad_local (u : Site n→G.Color) (v : Dir G n) : (represent ∘ radLog u v)=ᶠ[𝓝 0] spunt u v := by
  have he (e : Edge (Site n)) : Tendsto (fun t=> spunt u v t e) (𝓝 0) (𝓝 1) := by
     apply (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr
     exact (Eq.symm (congr_arg (G.mat <| · e) (spunt_zero u v))) ▸ ((spunt_smooth u v e).contDiffAt (x:=0)).continuousAt
  filter_upwards [eventually_all.mpr fun i : Edge (Site n)=> (he i).eventually G.plog_right] with s hs
  funext e; unfold Function.comp; rw [Work.F03.represent_link, radLog, show axisEquiv.symm (coord e.2)=e.2 from axisEquiv.symm_apply_apply _,Prod.eta]; exact hs e

lemma rad_rate (u : Site n→G.Color) (v : Dir G n) : HasDerivAt (radLog u v) (v+tilt u) 0 := hasDerivAt_pi.mpr fun j=> by
   let e : Edge (Site n):=⟨j.1,axisEquiv.symm j.2⟩
   let w := (v+tilt u) j
   have hg' (z : G.Color) : HasDerivAt (fun t:ℝ=>G.mat (G.lieExp (t • z))) (G.colorMat z) 0 := by
      have hx : HasFDerivAt (fun a=>G.mat (G.lieExp a)) G.colorMat.toContinuousLinearMap ((fun t : ℝ=> t • z) 0) := by simp only [zero_smul]; exact G.expDiff_zero
      exact HasFDerivAt.comp_hasDerivAt (l:=fun a=>G.mat (G.lieExp a)) (f:=fun t=>t • z) (𝕜:=ℝ) 0 hx (f':=z) (by simpa only [one_smul] using (hasDerivAt_id' (0:ℝ)).smul_const z)
   have h₀ : HasDerivAt (fun t=>G.mat (spunt u v t e)) (G.colorMat w * G.mat (spunt u v 0 e)) 0 := by
       rw [spunt_zero]
       simp_rw [spunt_read,G.mat_mul]
       rw [show coord e.2=j.2 from axisEquiv.apply_symm_apply _,show (e.1,j.2)=j from rfl]
       convert ((hg' (u e.1)).mul (hg' (v j)) |>.mul (hg' (-(u (e.1+step e.2))))) using 1
       all_goals try rfl
       all_goals try
          simp only [w,tilt,Pi.add_apply,Pi.mul_apply,zero_smul,G.mat_lieExp_zero,G.mat_one,map_add,map_sub,map_neg,Pi.one_apply,mul_one,one_mul]
          unfold e; abel
   change HasDerivAt (fun t=> G.plog (G.mat (spunt u v t e))) (w) 0
   have hg := Push.Loops.delta_rate (v:=fun t=>spunt u v t e) h₀
   exact hg.congr_of_eventuallyEq (Eventually.of_forall fun t=> (congr_arg (G.plog ∘ G.mat) (show _= spunt u v t e from by rw [show spunt u v 0=1 from spunt_zero ..]; simp)).symm)

section abstr
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : ℕ→E→F} {k : ℕ} (h : Junction f g (k-1)) (ha : lucid f) (hb : lucid g)
variable (u : ℝ→E) (z : E) {v : E} (ht : ContDiffAt ℝ ω u 0) (hr : deriv u 0=v) (hz : u 0=0)
   (hf : ∀ᶠ i in atTop, (f i ∘ u)=ᶠ[𝓝 0] (fun t : ℝ=> f i (t • z))) (hg : ∀ᶠ i in atTop, (g i ∘ u)=ᶠ[𝓝 0] (fun t : ℝ=> g i (t • z)))
   {A B : Tensor.T E F k} (hA : Tendsto (fun i=>spray f k i) atTop (𝓝 A)) (hB : Tendsto (fun i=>spray g k i) atTop (𝓝 B))

def discrep {k} (U V : Tensor.T E F k) (v : E) := Tensor.diagonal U v - Tensor.diagonal V v
include h ha hb ht hr hz hf hg hA hB
set_option maxHeartbeats 500000 in
lemma along_orbit (hk : 1 ≤ k) : discrep A B z=discrep A B v := by
   have hval (w) : Tendsto (fun i=> discrep (spray f k i) (spray g k i) w) atTop (𝓝 (discrep A B w)) := (view_cont.continuousAt.tendsto.comp (hA.prodMk_nhds (tendsto_const_nhds (x:=fun _=>w)))).sub (view_cont.continuousAt.tendsto.comp (hB.prodMk_nhds tendsto_const_nhds))
   have hpath {v' : ℝ→E} (hv : v' 0=0) (hh:ContDiffAt ℝ ∞ v' 0) := faa_lead ha hb
        (show lucid (fun _=>v') from Eventually.of_forall fun _=>hh) (show lucid (fun _=>v') from Eventually.of_forall fun _=>hh) (Eventually.of_forall fun _=>hv) (Eventually.of_forall fun _=>hv) h hk (fish · v') ⟨A,hA⟩ ⟨B,hB⟩ (fun _ _ => ⟨tendsto_const_nhds,tendsto_const_nhds⟩) (hval _)
   let t (s : ℝ) := s • z
   have h₁ : deriv t 0=z := by have hh := (hasDerivAt_id' (0:ℝ)).smul_const z; simpa only [one_smul ℝ] using hh.deriv
   have hT := hpath (v':=t) (zero_smul ..) (contDiffAt_id.smul contDiffAt_const)
   have hP := hpath (v':=u) hz (ht.of_le le_top)
   have hv (s : ℝ→E) : fish 1 s = deriv s (0:ℝ) := congr_fun iteratedDeriv_one 0
   rw [show fish 1 t=z from (hv t).trans h₁] at hT; rw [show fish 1 u=v from (hv u).trans hr] at hP
   exact tendsto_nhds_unique hT (hP.congr' ((hf.and hg).mono fun i hi=> congr_arg₂ (·-·) ((hi.1.iteratedDeriv k).eq_of_nhds) ((hi.2.iteratedDeriv k).eq_of_nhds)))

end abstr

lemma gauge_null {M M' : ℕ→PathData G} {p σ C Λ σ' C' Λ'} {W X}
   (h : Passing M W σ C Λ p) (h' : Passing M' X σ' C' Λ' p) (k : ℕ) (v : Dir G n) (hk : 1 ≤ k) (u : Site n→G.Color)
   (hu : Junction (fun i=>knotted n p (M i)) (fun i=>knotted _ p (M' i)) (k-1)) :
   discrep (Passing.planeTensor n k h) (Passing.planeTensor n k h') v = discrep (Passing.planeTensor n k h) (Passing.planeTensor n k h') (v+tilt u) := by
     refine along_orbit hu (h.groomed n) (h'.groomed n) (radLog u v) v (radSmooth ..) (rad_rate ..).deriv (rad_zero ..) ?_ ?_ (h.mainLimit n k|>.1) (h'.mainLimit n k|>.1) hk
     apply h.mask.mono
     on_goal 2 => apply h'.mask.mono
     all_goals
       intro i hW
       filter_upwards [rad_local u v] with t ht
       unfold knotted; dsimp only [Function.comp_apply] at *; have hk := Work.F05.mainTerm_gauge hW (represent (t • v)) (G.lieExp ∘ fun i=> t • u i); rw [ht]; exact hk

lemma loop_null_gauge {M M' : ℕ→PathData G} {p σ C Λ σ' C' Λ'} {W X}
   (h : Passing M W σ C Λ p) (h' : Passing M' X σ' C' Λ' p) (k : ℕ) (v : Dir G n) (hk : 1 ≤ k) (u : Site n→G.Color)
   (hu : Junction (fun i=>tread n (M i)) (fun i=>tread _ (M' i)) (k-1)) :
   discrep (Passing.spiralTensor n k h) (Passing.spiralTensor n k h') v = discrep (Passing.spiralTensor n k h) (Passing.spiralTensor n k h') (v+tilt u) := by
     refine along_orbit hu (h.loop_groomed n) (h'.loop_groomed n) (radLog u v) v (radSmooth ..) (rad_rate ..).deriv (rad_zero ..) ?_ ?_ (h.loopLimit n k|>.1) (h'.loopLimit n k|>.1) hk
     apply h.mask.mono
     on_goal 2 => apply h'.mask.mono
     all_goals
       intro i hW
       filter_upwards [rad_local u v] with t ht
       unfold tread; dsimp only [Function.comp_apply] at *; have hk := Work.F05.loop_gauge hW (represent (t • v)) (G.lieExp ∘ fun i=> t • u i); rw [ht]; exact hk

end YM.UVExt.Paths
