import YM.Euclid.Differential
import YM.Extraction.Round
import YM.Integration.WilsonSeparatedLatticeStencil
/-!
# Tensoring accuracy across ownership pad at the assembled f. Signed high-order coordinates.
No assumption of monotone positive f extension. Uses Taylor on successor of p; only N-stage radiation after physical UV. **Coefficients not altered**.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SignedWilsonExpansion.Camera.Ping
open Function Set Filter Metric Asymptotics
open Contacts.Mat Lattice Extraction Integration Integration.WilsonSeparatedLatticeStencil
open scoped Topology ContDiff BigOperators Classical
variable {ι:Type*}{F:Filter ι}{n b:ℕ} {δ θ:ι→ℝ} {Q K:Set (Points n)}
abbrev Rod (n:ℕ):= Fin n × Axis
-- admissible interpolation line *at* arbitrary chosen point.
def beams (x:Points n)(j: Rod n)(δ t:ℝ):= x+ t • (δ • Points.direction j.1 j.2)
abbrev slice (j:Rod n)(x:Points n):ℝ:= x j.1 j.2
private lemma beam_zero (x:Points n)(j:Rod n)(δ:ℝ): beams x j δ 0=x:= by rw [beams,zero_smul,add_zero]
private lemma drift (x:Points n)(j:Rod n)(δ t:ℝ):slice j (beams x j δ t)= slice j x+t*δ:=by simp [slice,beams,Points.direction,PiLp.single_apply]
private lemma mute (x:Points n)(i j: Rod n)(h:i≠j)(a t:ℝ): slice j (beams x i a t)= slice j x:=by
    by_cases hx:i.1=j.1
    · simp only [slice, beams, PiLp.add_apply, PiLp.smul_apply, Points.direction,hx,PiLp.single_apply]; have hz:j.2≠i.2:= fun he=> h (Prod.ext hx he.symm); simp [hz]
    simp [slice,beams,Points.direction,PiLp.single_apply,hx]
private lemma unitP (i:Rod n): ‖Points.direction i.1 i.2‖=1:=by simp [Points.direction]
private lemma room {x:Points n}(p:x∈ K){j:Rod n}{ δ t σ b:ℝ}(h: 0<δ) (w:t∈ Icc 0 b)(u:b * δ ≤ σ) : beams x j δ t∈ cthickening σ K :=by
    apply mem_cthickening_of_dist_le _ x _ _ p; rw [dist_eq_norm,beams,add_sub_cancel_left,norm_smul, norm_smul,unitP,Real.norm_of_nonneg h.le,Real.norm_of_nonneg w.1,mul_one]; exact (mul_le_mul_of_nonneg_right w.2 h.le).trans u
abbrev tagMask (I:Finset (Rod n))(x:Points n)(t:ℝ): Prop:= ∀ j∉ I,∃ k:ℤ,slice j x=t*k
private lemma full_mesh {x:Points n}{t:ℝ}(h:tagMask ∅ x t): ∃ y:Fin n→ Cover,x=Extraction.tag t y:=by
    choose k w using fun j:Rod n=> h j (Finset.notMem_empty j); let y(i:Fin n)(a:Axis):ℤ:= k (i,a); exact ⟨ y,PiLp.ext fun i=> PiLp.ext fun a=> w (i,a) ⟩
private lemma deeper {x:Points n}{t a:ℝ} (j:Rod n)(I:Finset (Rod n))(h:tagMask (insert j I) x t)(w:∃ u:ℤ,slice j x+a*t=t*u): tagMask I (beams x j t a) t:=by
   intro i hi; by_cases h':j=i; · subst i; rwa[drift]
   rw [mute x j i h']; exact h i (fun a=> ( Finset.mem_insert.mp a ).elim (Ne.symm h') hi )
variable (f: Points n→ℂ){u x:Points n}{t T D A:ℝ}(p:Tendsto δ F (𝓝 0))
abbrev along (x u:Points n)(m:ℕ)(s:ℝ) := iteratedFDeriv ℝ m f (x+s • u) (fun _=> u)
private lemma along_deriv {m:ℕ} (P:ContDiffAt ℝ ∞ f (x+t • u)): HasDerivAt (along f x u m) (along f x u (m+1) t) t :=by
   unfold along; rw [iteratedFDeriv_succ_apply_left]; exact (ContinuousMultilinearMap.apply ℝ _ ℂ (fun _=> u)).hasFDerivAt.comp_hasDerivAt t ((P.differentiableAt_iteratedFDeriv (m:=m) (by exact_mod_cast ENat.coe_lt_top _)).hasFDerivAt.comp_hasDerivAt t (show HasDerivAt (fun t:ℝ=> x + t • u) u t from by simpa using! (((hasDerivAt_id' t).smul_const u).const_add x ))) -- parse
private lemma wall {m:ℕ}{j: Rod n}(u:‖iteratedFDeriv ℝ m f (beams x j t T)‖≤ D)(w:0≤ t) : ‖along f x (t • Points.direction j.1 j.2) m T‖≤ D*t^m:=by
    refine ( ( iteratedFDeriv ℝ m f _ ).le_opNorm (fun _=> t • Points.direction j.1 j.2) ).trans ?_; simpa only [beams,Finset.prod_const, Finset.card_univ,Fintype.card_fin,norm_smul,unitP,Real.norm_of_nonneg w,mul_one] using mul_le_mul_of_nonneg_right u (pow_nonneg w m) -- rw goal first
-- local billing. centers arbitrary. Choose arities & link for all off-grid points. scalar to vector. radius(width*(n+1)) uniform at same scale
variable (g:ι→ Points n→ℂ) (S:∀ᶠ i in F,∀ x∈ interior Q, ContDiffAt ℝ ∞ (g i) x)(D₀:∃ C:ℝ,0≤ C∧ ∀ᶠ i in F,∀ x∈ interior Q,‖iteratedFDeriv ℝ (b+1) (g i) x‖≤ C)
def shown (F:Filter ι)(Q:Set (Points n)) (j:ι→ Points n→ℂ)(θ δ:ι→ℝ): Prop:= ∀ ε:ℝ,0<ε→ ∀ᶠ i in F,∀ y:Fin n→ Cover,Extraction.tag (δ i) y∈ Q→ ‖j i (Extraction.tag (δ i) y)‖≤ ε*‖θ i‖
variable (B : shown F Q g θ δ) (ρ: (δ^(b+1))=o[F] θ) (hδ: ∀ᶠ i in F,0<δ i)
private lemma enough (M: Nodes b T)(j:Rod n)(w:0< t)(d:D≥0)(h:∀ s∈ Icc 0 T,ContDiffAt ℝ ∞ f (beams x j t s))(u:∀ s∈ Icc 0 T, ‖iteratedFDeriv ℝ (b+1) f (beams x j t s)‖≤ D) (h':∀ i,‖f (beams x j t (M.v i))‖≤ A) : ‖f x‖≤ ((↑( b+1 ):ℝ)*T^b)*( D*t^(b+1)*(T^(b+1)/(b.factorial:ℝ))+ A):=by
   let Y := along f x (t • Points.direction j.1 j.2); have hp:= WilsonSeparatedLatticeStencil.error M Y ( D*t^(b+1) ) (by positivity) (fun i hi _ _=>along_deriv f ( h i hi )) (fun i hi=> wall f ( u i hi ) w.le)
   let P:= ∑ i:Fin (b+1), bleed M.v i • Y 0 (M.v i); have hP:T≥0:= (M.starts 0).1.trans (M.starts 0).2; have hu: ‖P‖≤ ((↑( b+1 ):ℝ)*T^b)*A:=by
      refine (norm_sum_le ..).trans (( Finset.sum_le_sum (g:=fun _=> T^b*A) (fun i _=> ?_) ).trans_eq (?_)); rw [ norm_smul ]; exact mul_le_mul (weight M i) (by simpa only [Y,along, iteratedFDeriv_zero_apply] using! h' i) (norm_nonneg _) (by positivity)
      simp [mul_assoc]
   rw [show f x = Y 0 0 from by simp [Y,along] ]; exact (norm_le_norm_sub_add _ P).trans (( add_le_add hp hu ).trans_eq (mul_add ..).symm)
include p hδ S D₀ B ρ
private lemma thickGets (I:Finset (Rod n))(ε:ℝ)(hp:0<ε)(r:IsCompact K)(w:K⊆interior Q): ∀ᶠ i in F,∀ x∈K,tagMask I x (δ i)→ ‖g i x‖≤ ε* ‖θ i‖:=by
    induction I using Finset.induction_on generalizing K ε with
    | empty=>
       filter_upwards [ B ε hp ] with i h x hx hv; obtain ⟨y,rfl⟩:= full_mesh hv; exact h y ( interior_subset (w hx) )
    | insert j I k ih=>
       let N:= clusterRadius (Fin 0) b; have hN:N>0:= clusterRadius_pos; let K' :ℝ := (↑(b+1):ℝ)*N^b; have hx:0<K':= mul_pos (by positivity) (pow_pos hN _); obtain ⟨ζ,hζ,hy⟩:= r.exists_cthickening_subset_open isOpen_interior w
       let V:= cthickening ζ K; obtain ⟨C,a,u⟩:=D₀; let U:=N^(b+1)/(b.factorial:ℝ); let T:= C*U +1; have he:C*U≤T:= le_add_of_nonneg_right zero_le_one; have hT:0<T:=by unfold T U; positivity
       let E:= ε/(2*K'); have hp':E>0:= div_pos hp (by positivity); have hT':= ρ.bound (div_pos hp' hT); filter_upwards [ ih E hp' r.cthickening hy, S, u, hT', hδ,(p.eventually_lt_const (div_pos hζ hN)) ] with i hi h0 u hv ht h x q k0; obtain ⟨M,y,hB⟩:= WilsonSeparatedLatticeStencil.nodes b (slice j x) (δ i) ht (fun _ : Fin 0=> 0)
       -- binder conflict
       have hw(s:ℝ)(hs:s∈ Icc 0 N) : beams x j (δ i) s∈ V:= room q ht hs ( (lt_div_iff₀ hN).mp h |>.le |> fun v=>by rwa [mul_comm] ); refine ( enough (g i) M j ht a (fun i' p'=>?_ ) (fun v p=> u _ ( hy ( hw v p ) )) (fun v=>hi ( beams x j _ _ ) ( hw _ ( M.starts v ) ) (deeper j I k0 ( y v ).1)) ).trans (?_); · exact h0 _ (hy (hw i' p'))
       change ‖(δ i)^(b+1)‖ ≤ E/T*_ at hv; rw [Real.norm_of_nonneg (by positivity)] at hv; calc
          K' * (C*(δ i)^(b+1)*U+ E*_) ≤ K'*( E*‖θ i‖ + E*‖θ i‖):= mul_le_mul_of_nonneg_left (add_le_add (calc
               C*(δ i)^(b+1)*U = C*U*(δ i)^(b+1):= by ring
               _ ≤ T*( E/T*‖θ i‖ ):= mul_le_mul he hv (by positivity) hT.le
               _=E*‖θ i‖:=by field_simp ) le_rfl) hx.le
          _= ε*‖θ i‖:= by unfold E; field_simp; ring
-- funder ✧ε already widens pad before buying Era order. apply any β lifecycle Fltr gain
lemma extendsOn (r:IsCompact K)(u:K⊆ interior Q) (ε:ℝ)(ht:0<ε): ∀ᶠ i in F,∀ x∈K,‖g i x‖≤ ε*‖θ i‖:= ( thickGets p g S D₀ B ρ hδ Finset.univ ε ht r u ).mono fun i h x hx=> h x hx fun _ k=> False.elim ( k ( Finset.mem_univ _ ) ) -- check include order
end YM.SignedWilsonExpansion.Camera.Ping
