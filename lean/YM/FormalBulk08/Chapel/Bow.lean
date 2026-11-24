import YM.FormalBulk08.Chapel.Raisin

/-! Root assembly from template dollars. Quantify over arbitrary analytic
moments on Gauss h through prescribed strips. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Chapel
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Next.Free RG Precision
open Lotus Shore Mesa Gorge City Cork Rift Lava
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}{σ η B C K : ℝ}{m r:ℕ}{L : Side}{I J : Type} {V : Type*}

lemma knox_tsum (D:Reach V) (p:V) (A:I→ ℝ)(B:I→ Tile V m)(hp:0≤η)(h:∀ i,Knoxville D η p (B i) (A i)) {C:ℝ}(he:0 ≤ C)(hc:(∑' i,ENNReal.ofReal (A i))≤ENNReal.ofReal C):
   Knoxville D η p (fun v=>∑' i,B i v) C ∧ ∀ v,Summable (fun i=> B i v) := by
    let F (v:chain V m):=Gorge.shine η (wide D (Fin.cons p v : chain V (m+1)))
    have hh:(∑' v,∑' i,F v*‖B i v‖ₑ)≤ _:= le_trans (b:=∑' i,ENNReal.ofReal (A i)) (by rw [ENNReal.tsum_comm (f:=fun v (i:I)=>_)]; exact ENNReal.tsum_le_tsum fun i=>(h i).2) hc
    refine ⟨⟨he,le_trans ?_ hh⟩,fun v=> ?_⟩
    · apply ENNReal.tsum_le_tsum;intro v; rw [ENNReal.tsum_mul_left]; exact mul_le_mul_right enorm_tsum_le_tsum_enorm _
    refine (tsum_enorm_ne_top_iff_summable_norm.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((le_trans ?_ (ENNReal.le_tsum (f:=fun v=>∑' i, F v * ‖B i v‖ₑ) v)).trans hh))).of_norm
    apply ENNReal.tsum_le_tsum; intro i;exact le_mul_of_one_le_left zero_le (shine_plus η hp _)

def glassTail (S : Cross L I J)(x: Biglot I)(T:Tile (Biglot I) (m+1))(t:chain I m):Tile (Biglot J) m := fun v=>∑' w:cloud m,rowC T x t w*candor S x.1 t w v

variable [Fintype I][Fintype J]
omit [Fintype I] [Fintype J] in
lemma pose_sharp (h:0<σ)(hs:0≤η)(_hc:0≤C)(d:ℕ) {M E:ℝ}(_hM:0≤M) (hE:0≤E) (S:Cross L I J)(_hw:Threshold σ η m L)(_ho:Odd L.val)(_H:gauss S η C d)(x:Biglot I)(u:Biglot J)(t:chain I m)
   (ha:∀ w:cloud m, Knoxville (fame _) η (piz L x u.2) (partD S x.1 t d w) (Real.exp (osc σ m * size w)*(E*(L.val:ℝ)⁻¹^(m+d))))
   {T : Tile (Biglot I) (m+1)}(ht:Bail (fame _) σ T B)(hg:∀ p∈trimmed (Fin m×Axis) d, |piles T x t p| ≤ M)
   {Q:ℝ}(hq:∀ p∈trimmed (Fin m×Axis) d, Knoxville (fame _) η (piz L x u.2) (gang (candor S x.1 t) (roll p) 0) Q)(hh:0≤Q) :
   Knoxville (fame _) η (piz L x u.2) (glassTail S x T t) (B*(E*(L.val:ℝ)⁻¹^(m+d)) + (trimmed (Fin m×Axis) d).card * (M*Q)) := by
    let a:= rowC T x t; let X:= candor S x.1 t; let P (w:cloud m)(v):ℝ:= a w*party d X w v; let F (w:cloud m):= a w • partD S x.1 t d w
    let y:=piz L x u.2; let g (v:chain (Biglot J) m):=∑' i,F i v
    let W:= E*(L.val:ℝ)⁻¹^(m+d);have hp:0≤W:= by unfold W; positivity
    obtain ⟨hb,Hs⟩:=knox_tsum (fame _) y _ F hs (fun w: cloud m=> (ha w).smul (a w)) (show 0≤ B*W from mul_nonneg ht.1 hp) (by
       rw [ENNReal.ofReal_mul ht.1]; refine le_trans ?_ (mul_le_mul_left (cost_rowC x t (osc σ m) (peel m h.le) (osc_pos m h|>.le) T ht) _); rw [←ENNReal.tsum_mul_right]
       apply ENNReal.tsum_le_tsum; intro w; rw [ENNReal.ofReal_mul (abs_nonneg (a w)), ENNReal.ofReal_mul (Real.exp_pos _).le, ←Real.norm_eq_abs,ofReal_norm,mul_left_comm]; exact le_of_eq (mul_assoc ..).symm)
    let Z(p):= (gang X (roll p) 0)
    let U:= trimmed (Fin m×Axis) d;let z:Tile (Biglot J) m := ∑ p∈U,piles T x t p • Z p
    have hP v : Summable (fun w=> P w v) ∧ ∑' w,P w v=z v:= by
       have he: (fun w=> P w v)=(fun w=> ∑ p∈U,(a w*hat p w)* Z p v):= funext fun w=> by simp only [P,party,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum, mul_assoc,U,Z]
       have hl(p:Grades (Fin m × Axis)): Summable fun w=> (a w * hat p w)* Z p v:= (summableRow h (par_hat _) ht x t).mul_right _
       rw [he]; refine ⟨summable_sum (fun p _=>hl p),?_⟩; simp_rw [Summable.tsum_finsetSum (fun p _=>hl p),tsum_mul_right,z, Finset.sum_apply];rfl
    rw [show glassTail S x T t = g+z from ?hex]; refine Knoxville.add hb ?_
    have hf:= knox_sum U (fun p hp=> ((hq p hp).smul (piles T x t p)).mono (mul_le_mul_of_nonneg_right (hg p hp) hh)); apply hf.mono (le_of_eq ?_); simp [U]
    case hex=>
       ext v; rw [Pi.add_apply,glassTail,← (hP v).2]; unfold g;rw [←Summable.tsum_add (Hs v) (hP v).1];apply tsum_congr; intro w;change a w*X w v= a w*(X w v-party d X w v)+a w*party d X w v;ring
omit [Fintype I] [Fintype J] in
lemma curtain_tail (h:0<σ)(hs:0≤η)(hc:0≤C)(m d :ℕ)(hm:1≤m)(hd:d≤4-m) (G:Gauge):∃ D E : ℝ,0≤D∧0≤E∧∀ L:Side,Threshold σ η m L→ Odd L.val→∀ S:Cross L (Stationary.Loc G 1) (Stationary.Loc G 1), gauss S η C d→∀ T:Tile (edgeL G) (m+1), Agate T → Up T→Valed T →∀ B V :ℝ, Bail (fame _) σ T B → Bail (fame _) σ (tap T) V →∀ x: edgeL G,∀ u:edgeL G,∀ t:chain (Stationary.Loc G 1) m, Knoxville (fame _) η (piz L x u.2) (glassTail S x T t) (B*(E*(L.val:ℝ)⁻¹^(m+d))+D*V) := by
   let Y:=Stationary.Loc G 1
   obtain ⟨K,hK,H⟩:= cash_part (m:=m) (I:=Y) (J:=Y) h hs hc d; obtain ⟨F,hF,hX⟩:= curtain_owed d m hm hd G h
   obtain ⟨N,hN,Hn⟩:= cash_cove (m:=m) (I:=Y) (J:=Y) hs hc d; let n:ℝ:=(trimmed (Fin m×Axis) d).card
   have hn : 0≤n:=Nat.cast_nonneg _; refine ⟨n*F*N,K,by positivity,hK,fun L hp ho S hz T hT ht hv B V hb hW x u t=>?_⟩
   apply (pose_sharp h hs hc d (mul_nonneg hF hW.1) hK S hp ho hz x u t (fun w=> H L hp ho S hz x t w u) hb (hX V B T ht hT hb hW hv x t) (fun p hh=> Hn _ S hz ho _ _ _ ((trim_def ..).mp hh|>.le) u) hN).mono; change _+n*_≤ _; apply le_of_eq;ring
end YM.FormalBulk08.Chapel
