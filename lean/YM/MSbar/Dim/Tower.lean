import YM.MSbar.Dim.Plate
import YM.MSbar.Dim.Motion

/-! Dimensionally regularized integral independence of hat ambient subspace,
including rotate finite ε equal to the appropriate blockwise trace. Treat external labels possibly
abstract; support costs fixed for those calls. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Dim
open Function Set Filter Metric Complex MeasureTheory Symbol Submodule
open scoped Topology ContDiff BigOperators Classical NNReal InnerProductSpace
variable {m n : ℕ} {T : ℕ→ Type} {S : Motion T}
variable {F : ∀ m,T m × Hat m → ℂ} {K : ℝ}

-- radius may depend on external insertion, existence each m. Need uniform for plate.up? enough two.
abbrev above (S:Motion T)(x:T m) := S.move (up m) x

def request (S:Motion T)(F:∀ m,T m × Hat m → ℂ)(s:ℂ)(m:ℕ)(x:T m):= plate s (fun y=>F (m+1) (above S x,y))

lemma perp_turn (L: Move m n){v w:Hat n} (he:‖v‖=‖w‖)(hI:∀ x:Hat m, ⟪L x,v⟫_ℝ= ⟪L x,w⟫_ℝ) : ∃ U:Hat n ≃ₗᵢ[ℝ] Hat n, U v=w ∧ ∀ x:Hat m, U (L x)=L x:=by
    refine ⟨reflection (ℝ∙(v-w))ᗮ,reflection_sub he,fun x=> reflection_mem_subspace_eq_self ?_⟩
    exact mem_orthogonal_singleton_iff_inner_left.mpr (by rw [inner_sub_right,hI]; ring)

namespace Tower
variable (h : (S.prod vectors).Natural F)
include h
lemma rotate (V:Move m n) (a:T m)(x:Hat m): F _ (S.move V a,V x)=F _ (a,x) := h V (a,x)
lemma radial_point (x:T m){v w:Hat n} (V: Move m n) (he: ‖v‖=‖w‖)(hI:∀ y: Hat m,⟪V y,v⟫_ℝ = ⟪V y,w⟫_ℝ): F n (S.move V x,v)=F n (S.move V x,w):=by
    obtain ⟨U,rfl,hR⟩:= perp_turn V he hI
    have H := rotate h U.toLinearIsometry (S.move V x) v; rw [← S.together] at H
    exact H.symm.trans (congr_arg (fun (L:Move m n)=> F n (S.move L x,U v)) (DFunLike.ext _ _ fun x=> hR x))
lemma plans (x:T m) (q:Hat m) {v w:Plane} (he:‖v‖=‖w‖) : F _ (above S x, grow m (q,v))= F _ (above S x,grow m (q,w)):=by
    apply radial_point h x (up m)
    · apply (sq_eq_sq₀ (by positivity) (by positivity)).mp; rw [grow_sq,grow_sq]; simp [he]
    intro y; simp [grow_inner]
lemma prepares (x:T m) (he:0≤K) (ht:Vanish K (fun y=>F (m+1) (above S x,y)))(hh: ContDiff ℝ ∞ (fun y : Hat (m+1)=> F _ (above S x,y))) : Packed m K (fun y=> F _ (above S x,y)):=
    ⟨he,ht.compact.hasTemperateGrowth hh,ht,fun q t=>plans h x q (show ‖(-t) • axis‖=‖t • axis‖ by rw [neg_smul,norm_neg])⟩
private lemma coil (x:T m)(q:Hat m)(r:Plane)(t:ℝ): F _ (above S (above S x),push (m+1) (grow m (q,r),t))= F _ (above S x, push m (q, Real.sqrt (‖r‖^2+t^2))):=by
   let w:=Real.sqrt (‖r‖^2+t^2); let P:=push m (q,w); let Q:= grow m (q,r)
   let A:= (up (m+1)).comp (up m)
   rw [← rotate h (up (m+1)) (above S x) (push m (q,_))]; change F _ (_,grow _ (Q,t • axis))=F _ (_,grow _ (P,0))
   have he: S.move A x=above S (above S x):= S.together ..
   change F _ (above S (above S x),grow _ (Q,t • axis))=F _ (above S (above S x),grow _ (P,0)); rw [← he]; refine radial_point h x A ?_ (fun y=> ?_)
   · apply (sq_eq_sq₀ (by positivity) (by positivity)).mp; simp only [grow_sq,P,Q,push,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow, add_zero,norm_smul,axis_norm,mul_one]; rw [Real.norm_of_nonneg (show 0 ≤ w from Real.sqrt_nonneg _), Real.norm_eq_abs,sq_abs,Real.sq_sqrt (show 0≤‖r‖^2+t^2 by positivity)]; ring
   change ⟪grow _ (grow m (y,0),0),_⟫_ℝ = ⟪grow _ (grow m (y,0),0),_⟫_ℝ; simp [P,Q,push,grow_inner]
set_option maxHeartbeats 350000 in
private lemma reduced (x:T m) {H} (hB:Packed (m+1) H (fun y=> F _ (above S (above S x),y)))(hp:Packed m K (fun y=> F _ (above S x,y))) (q:Hat m) (s:ℂ) :
    (∫ a:Plane, face s (fun y=> F _ (above S (above S x),y)) (grow m (q,a)))=face s (fun y=> F _ (above S x,y)) q:=by
     let f(u:ℝ):= F _ (above S x, push m (q,u)); let g(y:Hat (m+1+1)):= F _ (above S (above S x),y); let r: Plane × ℝ → Hat (m+1) × ℝ:= fun p=> (grow m (q,p.1),p.2)
     let G: Plane × ℝ → ℂ:= g ∘ push _ ∘ r
     have h0 : HasTemperateGrowth (fun z: Plane × ℝ=>(q,z.1)):= by fun_prop
     have h1 : HasTemperateGrowth (fun z: Plane × ℝ=> grow m (q,z.1)):= (grow m).hasTemperateGrowth.comp h0
     have h2 : HasTemperateGrowth r:=tame_pair h1 tame_projR
     have hu:g.HasTemperateGrowth:= hB.smooth
     have hT : G.HasTemperateGrowth:= hu.comp (tame_push.comp h2)
     unfold face; rw [show s-↑(m+1:ℕ)=s-↑m-1 by push_cast;ring]
     exact descending (f:=f) (F:=G) ((hp.radius q).thicken (le_max_left K H)) hT (fun a=> ((hB.radius (grow m (q,a))).thicken (le_max_right K H))) (fun a=> coil h x q a) _
lemma reaches_up (x:T m) {H} (hB:Packed (m+1) H (fun y=> F _ (above S (above S x),y))) (hp:Packed m K (fun y=> F _ (above S x,y))) (s:ℂ) : request S F s _ (above S x)=request S F s _ x:= by
     let a:=face s (fun y=> F _ (above S (above S x),y)); have Ht:MeasurableEmbedding (grow m):= (grow m).toHomeomorph.measurableEmbedding
     have hm:=bearing m; have hh: Integrable (a ∘ grow m) := (hm.integrable_comp_emb Ht).mpr (hB.integrable s)
     unfold request plate; rw [← hm.integral_comp Ht]; refine (MeasureTheory.integral_prod (μ:=volume) (ν:=volume) _ hh).trans ?_; exact integral_congr_ae (Eventually.of_forall fun q=>reduced h x hB hp q s)
lemma rotated (L : Hat m≃ₗᵢ[ℝ] Hat m) (x) (s : ℂ) : request S F s _ (S.move L.toLinearIsometry x)= request S F s _ x:= by
     unfold request plate; rw [← L.measurePreserving.integral_comp L.toHomeomorph.measurableEmbedding]; refine integral_congr_ae (Eventually.of_forall fun v=>?_); dsimp only; unfold face
     obtain ⟨U,hU⟩:=spin_growth L (LinearIsometryEquiv.refl ℝ _)
     refine congr_fun (congr_arg radial ?_) _; ext1 t
     have hh:S.move U.toLinearIsometry (above S x)=above S (S.move L.toLinearIsometry x):=by
        unfold above; simp_rw [← S.together]; exact congr_arg (fun (V:Move m (m+1))=>S.move V x) (DFunLike.ext _ _ fun x=>hU (x,0))
     have he : U (push m (v,t))=push m (L v,t):= hU _
     rw [← hh,← he]; exact rotate h U.toLinearIsometry ..
lemma compact_lift (r : ℂ) (hs : ∀ i (x:T i), ∃ K:ℝ,Packed i K (fun y=>F (i+1) (above S x,y))) : S.Natural (request S F r):= S.reaches (fun _ U x=> rotated h U x r) (fun i x=> by obtain ⟨K,hB⟩:= hs _ x; obtain ⟨Q,hQ⟩:= hs _ (above S x); exact reaches_up h x hQ hB r)
-- No continued-hat ambiguity for true positive dimensions at R=m
lemma canonical (t : T m)(hv:Packed m K (fun y=> F _ (above S t,y))) : request S F (m:ℂ) _ t=∫ x: Hat m, F m (t,x):=(four_plane hv).trans (integral_congr_ae (Eventually.of_forall fun y=>rotate h (up m) t y))
end Tower
end YM.MSbar.Dim
