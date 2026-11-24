import YM.FVA2.DawnB
/-!
# Bounding the possibly-singular bare frame at zero from a *positive* comparator test

Only used there. No stability assumptions on Gram at positive order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GramB
open Function Filter Set MeasureTheory
open scoped Topology Classical ContDiff
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
local notation "Vₗ"=> LinearMap.BilinForm ℝ X
local notation "Op"=> X →L[ℝ] X
variable {u: LinearMap.BilinForm ℝ X} {P: X→L[ℝ] X}
-- positivity. `x=0` if its weight is zero. flatten.Isotropic enough.
omit [FiniteDimensional ℝ X] in
private lemma inner_k (R: Vₗ) (c s k:ℝ) (p q:X) : R (c • p+s • q) (c • p+k • q)=c*c*R p p+c*k*R p q+s*c*R q p+s*k*R q q:= by simp only [ map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul ]; ring
-- vanish.Backdrop
private lemma stopped {c:ℝ}(h:∀ p:X,u (c • p+P p) (c • p+P p)=c*c*u p p)(hv:∀ i:X,u i i=0→ i=0) (hP:IsNilpotent P): P=0:= by
    have hh (x) (hf:P (P x)=0): P x=0:= by
        let z:= P x; apply hv z _; by_cases hk:c=0; · simpa [z,hk] using h x
        let X':=u x x; let p':=u x z + u z x; let y:= u z z; have ht (a): u (x+a • z) (x+a • z)= X'+a*p'+a*a*y:= by obtain ht:= inner_k u 1 a a x z; unfold X' p' y; rw [one_smul] at ht; rw [ht]; ring -- X proof
        have hx(a:ℝ): c*c*(X'+(a+c⁻¹)*p'+(a+c⁻¹)*(a+c⁻¹)*y)= c*c*(X'+a*p'+a*a*y):= by
           let g:=x+a • z; obtain H:= h g; have hh:P g=z:= by unfold g; rw [ map_add,map_smul,hf, smul_zero,add_zero ];
           have he : c • g + P g=c • (x+(a+c⁻¹) • z):= by rw [hh,add_smul,← add_assoc,smul_add,smul_add,smul_add,smul_inv_smul₀ hk];
           rw [he,map_smul,map_smul,LinearMap.smul_apply,smul_eq_mul,smul_eq_mul,ht, show u g g=_ from ht a ] at H; rw [mul_assoc]; exact H
        obtain h0:= hx 0; obtain h1:= hx (-c⁻¹); ring_nf at h0 h1; field_simp at h0 h1; -- inspect
        change y=0; nlinarith only [h0,h1]
    obtain ⟨r,he⟩:= hP; ext p; suffices H: ∀ q,∀ v:X,(P^q) v=0→ P v=0 from H r p (by rw [he]; rfl); intro k; induction k with| zero=> intro v hv; have hu:v=0:= hv; rw [hu,map_zero]| succ k ih=> intro v h; rw [pow_succ] at h; exact hh v (ih (P v) h)
-- apply comp-limit. no sequences assumptions on matrices beyond comparison fact (induction application). internal supplier
variable {T: Type*} [NormedAddCommGroup T] [NormedSpace ℝ T][FiniteDimensional ℝ T]
variable (e:T→ₗ[ℝ](X →L[ℝ] X))(hp:Injective e)(x:ℕ→T) (k:ℕ) (hz:∀ i,e (x i)^k=0)
variable (f: LinearMap.BilinForm ℝ X)(ht: ∀ p,f p p=0→p=0) (g:ℕ→ LinearMap.BilinForm ℝ X)
variable (h:∀ u:ℕ→ℕ,Tendsto u atTop atTop →∀ p a, Tendsto a atTop (𝓝 p) → Tendsto (fun n=>g (u n) (a n) (a n)) atTop (𝓝 (f p p)))
   (hX :∀ p:X,Tendsto (fun n=> g n ( p + e (x n) p ) ( p + e (x n) p )) atTop (𝓝 ( f p p )))
include hp ht hz h hX
lemma quiet : Tendsto x atTop (𝓝 0) := by
    by_contra hc; have hv:∃ c:ℝ,0<c∧∃ᶠ i in atTop, c ≤ ‖x i‖:= by simpa [Metric.tendsto_nhds,not_forall,frequently_atTop] using hc
    obtain ⟨c,hc,hv⟩:= hv; let u(k:ℕ):ℝ:= (1+‖x k‖)⁻¹; let V:ℕ→ℝ × T:= fun k=> (u k, u k • x k)
    have h1 (i:ℕ): 0<u i:= by unfold u; positivity
    have hV(n:ℕ): u n+‖(V n).2‖=1:= by unfold V; rw [norm_smul_of_nonneg (h1 n).le]; unfold u; field_simp; -- linter
    have hs:∃ᶠ i in atTop,V i∈Set.Icc 0 ( (1+c)⁻¹ ) ×ˢ Metric.closedBall (0:T) 1 := hv.mono fun i hi=> by
        have hp1:= h1 i; refine ⟨⟨ hp1.le,?_⟩,?_⟩; · change (1+‖x i‖)⁻¹≤ _; exact inv_anti₀ (by linarith:0<1+c) (by gcongr)
        rw [ Metric.mem_closedBall,dist_zero_right ]; linarith only [ hV i,hp1 ]
    obtain ⟨⟨a,B⟩,⟨⟨ha,hL⟩,hB⟩,v,hU,hq⟩:= IsCompact.tendsto_subseq' (isCompact_Icc.prod (isCompact_closedBall ..)) hs -- check
    let A:= e B;   -- remove
    have hs': Tendsto (u ∘ v) atTop (𝓝 a):= Tendsto.fst_nhds hq; have hx : Tendsto (fun i=>(V (v i)).2) atTop (𝓝 B):= Tendsto.snd_nhds hq
    have ht': Tendsto (fun i=> e ((V (v i)).2)) atTop (𝓝 A):= e.toContinuousLinearMap.continuous.continuousAt.tendsto.comp hx
    have hR:A=0:= by
       refine stopped (P:=A) (u:=f) (c:=a) (fun p=>?_) ht ⟨ k,?_ ⟩
       · let H(n :ℕ):= u ( v n ); let q(i):= p+e (x (v i)) p;
         obtain hh : Tendsto (fun k=>g (v k) ( H k • q k ) ( H k • q k )) atTop (𝓝 (f (a • p + A p) (a • p + A p) )):= by
             apply h v hU.tendsto_atTop; have he: (fun i=> H i • q i)=(fun i=> H i • p + e ((V (v i)).2) p):= funext fun i=> by unfold V H q; simp only [ map_smul, _root_.smul_apply, smul_add ]; -- ok?
             rw [he]; exact (hs'.smul_const _).add ( (ContinuousLinearMap.apply ℝ X p).continuous.continuousAt.tendsto.comp ht' )
         apply tendsto_nhds_unique hh; simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,mul_assoc]; exact hs'.mul ( hs'.mul ((hX p).comp hU.tendsto_atTop))
       obtain hh:= ht'.pow k; have hz : ∀ i,e (V (v i)).2 ^ k=0:= fun i=> by change e ( u (v i) • x (v i)) ^ k=_; rw [map_smul, smul_pow, hz, smul_zero ];
       simp_rw [hz] at hh; exact tendsto_nhds_unique hh tendsto_const_nhds
    obtain hh:= tendsto_nhds_unique (hs'.add hx.norm) ( f:=fun i=> u (v i) + ‖(V (v i)).2‖ ) ( show Tendsto _ atTop (𝓝 1) from tendsto_const_nhds.congr (fun i=> (hV (v i)).symm) ); have h' : B=0:= hp (hR.trans (map_zero _).symm); rw [h',norm_zero,add_zero] at hh; change a ≤ _ at hL; rw [hh] at hL; exact hL.not_gt (inv_lt_one_of_one_lt₀ (by linarith))
end YM.FVA2.GramB
