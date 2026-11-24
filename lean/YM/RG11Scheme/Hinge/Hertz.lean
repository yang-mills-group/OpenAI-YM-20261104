import YM.RG11Scheme.Hinge.Values

/-! Product/dilation laws and compact bills. Orthogonal color-potential lines continue on the exterior with any derivative; no Fourier interpolation near the singularity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace YM.RG11Scheme.Hinge
open Function Set Filter MeasureTheory Maxwell Pert Full Align Mesh Next.Rank.Radian Stencil Stencil.Shot Stencil.Point Lattice
open scoped BigOperators Classical ContDiff Topology
variable {E F W:Type} [NormedAddCommGroup E][NormedAddCommGroup F][NormedAddCommGroup W]
   [NormedSpace ℝ E][NormedSpace ℝ F][NormedSpace ℝ W]
variable {T : Itinerary} {V U : Set E4} {g:ℕ→ Cover→E} {h:ℕ→ Cover→ F} {a:E4→E} {b:E4→F} {k:ℕ}

def stride (h:ℝ) (i:Axis)(g : Cover → E) (x:Cover) := h⁻¹ • (g (x+step i)-g x)
def pulse (T:Itinerary) (i:Axis)(f:ℕ→ Cover→E)(s:ℕ)(x:Cover):=stride (T.gap s) i (f s) x
lemma list_append (p : List Axis)(s:Axis)(h:ℝ)(g:Cover→ E)(_hp:h≠0)(x) :
     (h^(p++[s]).length)⁻¹ • go (p++[s]) g x = (h^p.length)⁻¹ • go p (stride h s g) x := by
   rw [go_concat]
   have he := go_map (Y:=E) ((h⁻¹ • LinearMap.id : E→ₗ[ℝ] E).toAddMonoidHom) (go [s] g) p x
   change go p (stride h s g) x=h⁻¹ • go p (go [s] g) x at he
   rw [he,List.length_append,pow_add, mul_inv,smul_smul,List.length_singleton, pow_one]
lemma dV_append (p:List Axis)(s:Axis): dV (p++[s]) a = dV p (grad s a) := by rw [dV,List.foldr_append];rfl
lemma Works.steps (hf:Works T V g a (k+1)) (i:Axis) : Works T V (pulse T i g) (grad i a) k := by
    refine ⟨fun x hx=> stroll [i] (hf.healthy _ hx),?_⟩
    intro σ hs z hz p he D hd;have hm:=hf.runs σ hs z hz p he (D++[i]) (by simpa using hd)
    simp only [list_append D i _ _ (T.positive _).ne',dV_append] at hm; exact hm
lemma stitched (hf:∀ z∈V,ContDiffAt ℝ ∞ a z) (h:∀ σ:ℕ→ℕ,Tendsto σ atTop atTop→∀ (z:E4), z∈V→∀ (p:ℕ→ Cover),Tendsto (fun i=>incVec (T.gap (σ i)) (p i)) atTop (𝓝 z)→Tendsto (fun i=>g (σ i) (p i)) atTop (𝓝 (a z))) (p:∀ i:Axis,(0<k)→ Works T V (pulse T i g) (grad i a) (k-1)):
     Works T V g a k := by
    refine ⟨hf,?_⟩
    intro σ hs x hx y he D hd
    cases D using List.reverseRecOn with
    | nil=> simpa only [List.length_nil,pow_zero,inv_one,one_smul,starting,dV,List.foldr_nil] using h σ hs x hx y he
    | append_singleton D d _ =>
       simp_rw [dV_append,list_append D d _ _ (T.positive _).ne']; have ht : D.length+1≤k:= by simpa only [List.length_append, List.length_singleton] using hd
       exact (p d (by omega)).runs σ hs x hx y he D (by omega)
lemma Works.replace (hf:Works T V g a k) {c:E4→E} (hV:IsOpen V) (h:∀ x∈V,a x=c x): Works T V g c k := by
    have hn (x) (hx:x∈V) : a=ᶠ[𝓝 x] c := Filter.Eventually.mono (p:=fun i=>i∈V) (hV.mem_nhds hx) h -- check
    refine ⟨fun x hx=>(hf.healthy _ hx).congr_of_eventuallyEq (hn x hx).symm,?_⟩
    intro σ hs z hz p u D hd; rw [← (crushed D (hn z hz)).eq_of_nhds];exact hf.runs σ hs z hz p u D hd

lemma continuous_applyT {P:E→L[ℝ]F→L[ℝ]W}: Continuous fun a:E×F=> P a.1 a.2:=by fun_prop
lemma Works.bilinear (hp:Works T V g a k)(hq:Works T V h b k)(hV:IsOpen V)(P:E→L[ℝ]F→L[ℝ]W) : Works T V (fun s p=>P (g s p) (h s p)) (fun x=>P (a x) (b x)) k := by
   induction k generalizing a g b h with
   | zero=> apply stitched (fun z hz=> (P.contDiff.contDiffAt.comp z (hp.healthy z hz)).clm_apply (hq.healthy z hz));
            · intro σ hs z hz p u; exact (continuous_applyT (P:=P) |>.continuousAt (x:=(a z,b z)) |>.tendsto.comp ((hp.at_point σ hs hz u).prodMk_nhds (hq.at_point σ hs hz u)))
            intro i H; omega
   | succ k IH=>
    refine stitched (fun z hz=> (P.contDiff.contDiffAt.comp z (hp.healthy z hz)).clm_apply (hq.healthy z hz)) (fun σ hs z hz p u=>?_) ?_
    · exact (continuous_applyT (P:=P) |>.continuousAt (x:=(a z,b z)) |>.tendsto.comp ((hp.at_point σ hs hz u).prodMk_nhds (hq.at_point σ hs hz u)))
    intro i _; rw [Nat.add_sub_cancel]
    let x := pulse T i (fun s p=>P (g s p) (h s p))
    have A := IH (hp.steps i) ((hq.cut Subset.rfl (Nat.le_succ k)).wander hV (step i))
    have B := IH (hp.cut Subset.rfl (Nat.le_succ k)) (hq.steps i)
    have hH : x=fun s p=> P (pulse T i g s p) (h s (p+step i)) + P (g s p) (pulse T i h s p) := by
       funext s p
       change (T.gap s)⁻¹ • (P (g s (p+step i)) (h s (p+step i))-P (g s p) (h s p)) = _
       unfold pulse stride; rw [P.map_smul,P.map_sub,(P (g s p)).map_smul,(P (g s p)).map_sub]
       simp only [sub_apply,smul_apply,smul_sub];abel
    refine Works.replace ?_ hV (a:=(fun r=>P (grad i a r) (b r)) + (fun r=>P (a r) (grad i b r))) ?_
    · change Works T V x _ k; rw [hH]; exact A.plus B hV
    intro z hz; have hu := (P.contDiff.contDiffAt.comp z (hp.healthy z hz)).differentiableAt (by decide); have he := (hp.healthy z hz).differentiableAt (by decide); have hb:=(hq.healthy z hz).differentiableAt (by decide)
    let r (w:E4):=P (a w)
    have hd:= hu.hasFDerivAt.clm_apply hb.hasFDerivAt
    unfold grad Analysis.D; erw [hd.fderiv]; simp only [Pi.add_apply,add_apply]
    rw [fderiv_comp z P.differentiableAt he,P.fderiv]; exact add_comm ..
lemma Works.minus (hp:Works T V g a k) (hV:IsOpen V) : Works T V (fun s p=> -(g s p)) (-a) k := hp.mapped hV (-ContinuousLinearMap.id ℝ E)

lemma Works.command (hp:Works T V g a k) {R:Set E4} (hr:IsCompact R)(hu:R⊆V) (D:List Axis)(hd:D.length≤k) : ∃ C>0, ∀ᶠ s:ℕ in atTop, ∀ p:Cover, incVec (T.gap s) p∈R → ‖go D (g s) p‖ ≤ C*(T.gap s)^D.length := by
   by_contra! hc
   have he (s:ℕ): ∃ v≥s,∃ p:Cover,incVec (T.gap v) p∈R ∧ ((s:ℝ)+1)*(T.gap v)^D.length< ‖go D (g v) p‖:= frequently_atTop.1 (hc ((s:ℝ)+1) (by positivity)) s
   choose v hv p ht hS using he
   obtain ⟨z,hz,y,hy,H⟩ := hr.isSeqCompact ht
   let σ:=v ∘ y
   have hh := hy.tendsto_atTop
   have hs : Tendsto σ atTop atTop := (tendsto_atTop_mono (f:=id) hv tendsto_id).comp hh
   have hu := hp.runs σ hs z (hu hz) (p ∘ y) H D hd |>.norm
   let B:= ‖dV D a z‖+1
   obtain ⟨i,hi,u⟩ := ((hu.eventually (ge_mem_nhds (lt_add_one ‖dV D a z‖))).and ((tendsto_natCast_atTop_atTop.comp hh).eventually (eventually_ge_atTop B))).exists
   have he:=T.positive (σ i)
   change ‖(T.gap (σ i)^D.length)⁻¹ • go D _ (p (y i))‖ ≤ B at hi
   rw [norm_smul,Real.norm_of_nonneg (by positivity),←div_eq_inv_mul] at hi
   have hx := (div_le_iff₀ (by positivity)).1 hi
   have hl := (hS (y i)).trans_le hx
   change _*T.gap (σ i)^_ < _*T.gap (σ i)^_ at hl ; exact (not_lt_of_ge (le_trans u (le_add_of_nonneg_right zero_le_one))) (lt_of_mul_lt_mul_right hl (pow_nonneg he.le _))
end YM.RG11Scheme.Hinge
