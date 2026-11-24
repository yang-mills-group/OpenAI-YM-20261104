import YM.FormalBulk08.Sable.Frozen

/-! Root testimonials & moment assembly. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sable
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Grail Work.F03 Work.F05 Work.F08
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{I J:Type}{m d e u:ℕ} {B σ η C:ℝ}{L:Side}
lemma sharpen (h:0<σ)(d:ℕ) (S:Cross L I J)(x:Biglot I)(u':Biglot J)(t:chain I m){M E:ℝ}(hE:0≤E)
    (ha:∀ w:cloud m, Knoxville (grain (fame _) 1) u (piz L x u'.2) (partD S x.1 t d w) (E*(1+(size w:ℝ))^u *(L.val:ℝ)⁻¹^(m+d)))
    {T:Tile (Biglot I) (m+1)}{Z:ℝ}(ht:Bail (fame _) σ T Z)(hZ:Bail (grain (fame _) 1) u T B)(hg:∀ p∈trimmed (Fin m×Axis) d,|piles T x t p|≤M) {Q:ℝ}(hq:∀ p∈trimmed (Fin m×Axis) d, Knoxville (grain (fame _) 1) u (piz L x u'.2) (gang (candor S x.1 t) (roll p) 0) Q)(hh:0≤Q): Knoxville (grain (fame _) 1) u (piz L x u'.2) (glassTail S x T t) (((1+(m:ℝ))^u*B)*(E*(L.val:ℝ)⁻¹^(m+d)) + (trimmed (Fin m×Axis) d).card * (M*Q)):= by
    let a:= rowC T x t; let X:= candor S x.1 t; let P (w:cloud m)(v):ℝ:=a w*party d X w v; let F (w:cloud m):= a w • partD S x.1 t d w
    let y:=piz L x u'.2; let g(v:chain (Biglot J) m):=∑' i,F i v
    let W:= E*(L.val:ℝ)⁻¹^(m+d); have hp:0≤W:=by unfold W; positivity
    let V:= (1+(m:ℝ))^u*B;have hv:0≤V:=mul_nonneg (by positivity) hZ.1
    obtain ⟨hb,Hs⟩:=knox_tsum (grain (fame _) 1) y _ F (Nat.cast_nonneg _) (fun w: cloud m=> (ha w).smul (a w)) (mul_nonneg hv hp) (by
       rw [ENNReal.ofReal_mul hv]; refine le_trans ?_ (mul_le_mul_left (hike x t u T hZ) _); rw [←ENNReal.tsum_mul_right]; apply ENNReal.tsum_le_tsum; intro w
       rw [show |a w| *(E* _*(L.val:ℝ)⁻¹^(m+d))=(1+(size w:ℝ))^u*(|a w| * W) by unfold W;ring,ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (abs_nonneg _),←Real.norm_eq_abs,ofReal_norm,mul_assoc]) -- parse
    let Z (p):=gang X (roll p) 0; let U:=trimmed (Fin m× Axis) d; let z:Tile (Biglot J) m:=∑ p∈U,piles T x t p • Z p
    have hP v: Summable (fun w=> P w v) ∧ ∑' w,P w v=z v := by
       have he: (fun w=> P w v)=(fun w=> ∑ p∈U,(a w*Chapel.hat p w)* Z p v):= funext fun w=> by simp only [P,party,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum, mul_assoc,U,Z]
       have hl(p:Grades (Fin m × Axis)): Summable fun w=> (a w*Chapel.hat p w)* Z p v:= (summableRow h (par_hat _) ht x t).mul_right _
       rw [he]; refine ⟨summable_sum (fun p _=>hl p),?_⟩; simp_rw [Summable.tsum_finsetSum (fun p _=>hl p),tsum_mul_right,z,Finset.sum_apply];rfl
    rw [show glassTail S x T t=g+z from (by ext v; rw [Pi.add_apply,glassTail,←(hP v).2]; unfold g;rw [←Summable.tsum_add (Hs v) (hP v).1];apply tsum_congr; intro w;change a w*X w v= a w*(X w v-party d X w v)+a w*party d X w v;ring)]
    refine Knoxville.add hb ?_; have hf:= knox_sum U (fun p hp=> ((hq p hp).smul (piles T x t p)).mono (mul_le_mul_of_nonneg_right (hg p hp) hh)); apply hf.mono (le_of_eq ?_); simp [U]
lemma needle (a:Loc G 1)(m u k:ℕ)(he: k≤ u)(hp:0<η)(hc:0≤C) : ∃ X Y:ℝ,0≤X ∧ 0≤Y ∧ ∀ L:Side,Odd L.val → ∀ S:Cross L (Loc G 1) (Loc G 1), gauss S η C k → ∀ x: Site L,∀ T:Tile (edgeL G) m, (∃ B σ:ℝ,0<σ ∧ Knoxville (fame _) σ (0,a) T B)→∀ A B:ℝ, Knoxville (grain (fame _) 1) u (0,a) T B → 0≤A → (∀ (i:chain (Loc G 1) m) t,t∈trimmed (Fin m×Axis) k → ‖tariffs (fun j:Fin m=> assigns (horn (aster t j) (i j))) T‖≤ A) → Knoxville (grain (fame _) 1) u (0,a) (upmost L x S T) (X*B*(L.val:ℝ)⁻¹^(m+k)+A*Y):= by
    obtain ⟨E,hE,H⟩:=frozen (I:=Loc G 1) (J:=Loc G 1) m u hp hc k he; obtain ⟨R,hR,Hr⟩:=cash_cove (I:=Loc G 1) (J:=Loc G 1) (m:=m) hp.le hc k
    let M:ℝ:= Fintype.card (chain (Loc G 1) m); let F:= trimmed (Fin m × Axis) k; let W:= sack u η*R; have hw: 0≤ W:= mul_nonneg (sack_pos u hp) hR
    refine ⟨M*E*(1+(m:ℝ))^u,M*F.card* W,by unfold M;positivity,by unfold M;positivity,fun L ho S hS x T ht A B hT ha hU=>?_⟩
    obtain ⟨Z,σ,hs,hx⟩:=ht; let V:edgeL G:=(lift x,a); let c:edgeL G:=(0,a); let p:=robot V (carries (lift x) T); have hl:=bot_arm V _ (knight (lift x) a T hx)
    have hp' := bot_arm V _ (fled (θ:=1) _ _ hT); have hz :piz L V a=c:=Prod.ext (by
       change rent L (lift x)=0; exact (rent_raw (0:Cover) (lift x) x (by simp)).2) rfl
    have hZ:= hS [] (Nat.zero_le _);rw [advanceC,List.length_nil,add_zero,pow_one] at hZ
    unfold upmost; rw [tale_gate S (lift x) a hZ hp.le (mul_nonneg hc (by positivity)) _ hs.le hx]
    have hx (i:chain (Loc G 1) m): Knoxville (grain (fame _) 1) u c (glassTail S V p i) (((1+(m:ℝ))^u*B)*(E*(L.val:ℝ)⁻¹^(m+k))+ F.card*(A*W)):= by
       rw [show c=piz L V a from hz.symm]; refine sharpen hs k S V c i hE (fun w=>H L ho S hS V _ w a) hl hp' (fun j hj=>?_) (fun j hj=> ?_) hw
       · rw [horn_test (lift x) a T j i hx hs]; exact hU i j hj
       exact sack_to u hp le_rfl (Hr L S hS ho V i j ((trim_def ..).mp hj|>.le) c)
    apply (knox_sum Finset.univ (fun i _=> hx i)).mono; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; change M*(_ + _) ≤ _; apply le_of_eq; ring
end YM.FormalBulk08.Sable
