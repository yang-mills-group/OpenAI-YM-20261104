import YM.MS.High.Balloon
/-!
# Limit jets and local spaces; a finite-rank request within an all-order induction
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.High
open Function Filter Set Finset Real Plane Wire Flux Domain LogTime LogTime.IntervalFamily Momentum
open Landau Detect Koszul Logarithm Color
open scoped Topology ContDiff
variable {G : Gauge} {x : ℝ} {F: Law G} {M : Reading G} {r s : ℕ} {b : Bool} {h d u:ℤ}

lemma slice_solid (hi:Mature M b r h) (hv:u≤h) (hd: ∀ t,Solid b (M t) d): Solid b (slice M b r u x) d:= by
   let S:=slice M b r u x; let K:=fun t:ℝ=> skin wfield u (M (x,t)); have hp (w: List (Lane4 G)) (hw:Course b w) (hr:w.length=r): Tendsto (fun t=>K t w) atTop (𝓝 (S w)):= accumulates hi hw hr x hv -- hw infer?
   have hh (w : List (Lane4 G)) (hw:Course b w) (he:w.length=r) t : ContDiff ℝ ∞ fun p=>M t (sail (ray w) p):= hi.smooth ℝ (ray w) (ray_course hw) (by simp [he]) t.1 t.2
   change Solid b S d; refine ⟨fun l i k r' he=>?_,fun w hw hD=> ?_,fun w hw a=>?_,fun w hw=>?_⟩
   · have hz:=course_swap b l r' i k he; by_cases hδ:(l++i::k::r').length=r
     · have hi' (t:ℝ) : K t (l++i::k::r')= cross (parity i.1) (parity k.1)*K t (l++k::i::r'):= skin_swap (hd _) _ _ _ _ he
       have hx:= hp _ he hδ; simp_rw [hi'] at hx; exact tendsto_nhds_unique hx ((hp _ hz (by simpa using hδ)).const_mul _)
     rw [show S (l++i::k::r')=0 from rank_slice (M:=M) _ he hδ,show S (l++k::i::r')=0 from rank_slice (M:=M) _ hz (by simpa using hδ),mul_zero]
   · by_cases hr:w.length=r; swap; exact rank_slice (M:=M) w hw hr
     have hx t:K t w=0:= skin_ghost (hd _) hw hD; have ht:= hp w hw hr; simp_rw [hx] at ht; exact tendsto_nhds_unique ht tendsto_const_nhds
   · change repeatC a S w= _; have hb l (h:paint l w) := paint_course (Eq.symm h) hw -- h.symm not defined?
     by_cases hr:w.length=r
     · have he := repeat_lim (F:=K) (K:=S) (w:=w) a (fun l h=> hp l (hb l h) ((paint_len _ _ h).trans hr));
       have hx t: repeatC a (K t) w=K t w:=skin_color (hd _) hw (fun u h=> hh u (hb u h) ((paint_len _ _ h).trans hr) _) _
       simp_rw [hx] at he; exact tendsto_nhds_unique he (hp w hw hr)
     have hz l (h:paint l w): S l=0:=rank_slice (M:=M) l (hb l h) (paint_len _ _ h ▸ hr); exact (paint_zero a w hz).trans (hz w rfl).symm
   have hh' : Course b (invertMom w):= fun h=>by rw [net_invert,hw h];  exact neg_zero
   by_cases hl:w.length=r
   · have ht:= hp (invertMom w) hh' (by simp [invertMom,hl]); have he t: K t (invertMom w)=star (K t w):= skin_shadow (hd _) hw (hh w hw hl _); simp_rw [he] at ht; exact tendsto_nhds_unique ht ((continuous_star.continuousAt.tendsto.comp (hp w hw hl)))
   rw [show S w=0 from rank_slice (M:=M) w hw hl, star_zero]; exact rank_slice (M:=M) _ hh' (by simp [invertMom,hl])
lemma slice_signed (hi:Mature M b r h) (hv:u≤h) (hd: ∀ t,SignedScope b (M t)): SignedScope b (slice M b r u x):= by
   intro k w hw; by_cases he:w.length=r
   · have ht:=accumulates hi (sign_course k hw) (by simp [he]) x hv; have hv' := ht.const_mul (w.map (negateField k)).prod
     simp_rw [skin_signed (hd _) w hw] at hv'; exact tendsto_nhds_unique hv' (accumulates hi hw he x hv)
   rw [rank_slice w hw he,rank_slice _ (sign_course k hw) (by simp [he]),mul_zero]
-- stamp interpolation transfer. Real-λ polynomial values (works complex row).
lemma eval_line (M: Reading G) {N:ℕ} (hp:(fun v:ℝ=>fun t:ℝ=> M (v,t)) ∈ interest N _) (x t : ℝ) (w : List (Lane4 G)):
    M (x,t) w= ∑ i∈Finset.range N, (plate N i).eval x • M ((i:ℝ),t) w:= by
   have hh:= congr_fun (congr_fun (interpret hp x) t) w; exact (Eq.trans hh (by unfold evaluate; simp only [Finset.sum_apply,Pi.smul_apply]))
lemma read_smul {f : ℝ→ℂ} (p:ℝ) (s) (hf:ContDiff ℝ ∞ f): reading s (fun x=>p • f x)= p • reading s f:= by unfold reading; rw [iteratedDeriv_fun_const_smul (hf.contDiffAt.of_le (by exact_mod_cast le_top)),smul_comm]
lemma slice_interp (hi:Mature M b r h) (hv:u≤h) {N:ℕ} (hp:(fun v:ℝ=>fun t:ℝ=> M (v,t)) ∈ interest N _) (x:ℝ): slice M b r u x= evaluate N (slice M b r u) x:= by
    ext w; unfold evaluate; simp_rw [Finset.sum_apply,Pi.smul_apply]; classical
    by_cases hδ: Course b w; swap; · simp only [slice_drop _ hδ, smul_zero,sum_const_zero]
    by_cases he:w.length=r; swap; · simp only [rank_slice _ hδ he, smul_zero,sum_const_zero]
    have ht (t:ℝ): skin wfield u (M (x,t)) w=∑ i∈ Finset.range N,(plate N i).eval x • skin wfield u (M ((i:ℝ),t)) w:= by
       unfold skin; split_ifs with h
       · simp_rw [torch_at]; let M1 (i:ℝ) (k:ℝ):= M (i,t) (sail (ray w) k)
         have hx i : ContDiff ℝ ∞ (M1 i):= hi.smooth ℝ (ray w) (ray_course hδ) (by simp [he]) i _
         simp_rw [eval_line M hp x t]; let P (i:ℕ) := (plate N i).eval x
         let L:=(u-fieldDim wfield w).toNat
         change reading L (fun u=> ∑ i∈ Finset.range N,P i • M1 i u)=∑ i∈ Finset.range N,P i • reading L (M1 (i:ℝ)); rw [read_sum ..];
         · exact Finset.sum_congr rfl fun i _=> read_smul _ _ (hx _)
         intro i hi; exact (hx _).const_smul _
       simp
    have hh:=accumulates hi hδ he x hv; simp_rw [ht] at hh; exact tendsto_nhds_unique hh (tendsto_finsetSum _ fun i _=> (accumulates hi hδ he (i:ℝ) hv).const_smul _)
lemma slice_ready (hi:Mature M b r h) (hv:u≤h) (he: stamp M): Logarithm.Ready (slice M b r u):= by
    obtain ⟨N,H⟩:= he; exact funext (slice_interp hi hv H) ▸ eval_ready N (slice M b r u) -- dependent direction
end YM.MS.High
