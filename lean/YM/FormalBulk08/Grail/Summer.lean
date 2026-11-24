import YM.FormalBulk08.Grail.Duck

/-! Exact linearity including T=0, and full cost. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Grail
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {I J:Type}{G:Gauge}{m d D l j r:ℕ}{A B C E η σ θ:ℝ}{a:Loc G 1}{L:Side}{x:Site L}{f:Cross L (Loc G 1) (Loc G 1)}
lemma loom_add (a: Loc G 1)(S T:Tile (edgeL G) m)(h:Knoxville (fame _) σ (0,a) S A)(ht: Knoxville (fame _) θ (0,a) T B)(hp:0≤η)(hr:0≤σ)(hθ:0≤θ)(he:f.strip η C)(hc:0≤C): upmost L x f (S+T)=upmost L x f S+upmost L x f T:= by
    funext v; let X := (show edgeL G from (lift x,a));
    have hz (φ C:ℝ)(hφ:0≤φ)(Y:Tile (edgeL G) m)(H:Knoxville (fame _) φ (0,a) Y C): Summable (fun w=> carries (lift x) Y w*∏ i,Chapel.merit f (w i) (v i)):= by
       apply lenses _ _ (fun _=> center_row _ he hp hc) (carries _ Y) (C:=C); intro w; exact le_trans (le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (show 0≤φ*herb (fame _) X w from mul_nonneg hφ (Nat.cast_nonneg _)))) (penn_chill w (knight (lift x) a Y H))
    rw [Pi.add_apply]; unfold upmost pearl;rw [←Summable.tsum_add (hz _ _ hr S h) (hz _ _ hθ T ht)]; refine tsum_congr fun w=>?_ ; exact add_mul ..
lemma solas (T:Anthem D G)(h: Clef a T r)(x:Site L)(he:f.strip η A)(hc :0≤A)(hy:0≤η)(e l:ℕ) : IsLinearMap ℝ (fun p=> upmost L x f (T p e l)) := by
   obtain ⟨s,C,hs,hC,H⟩:=h.fare.2.2 e l
   refine ⟨fun i j=>?_,fun c i=>?_⟩
   · rw [h.map_add]; exact loom_add a _ _ (H i) (H j) hy hs.le hs.le he hc
   rw [h.map_smul]; ext v; unfold upmost pearl; simp only [Pi.smul_apply, smul_eq_mul,←tsum_mul_left]; refine tsum_congr fun _=>?_ ; exact mul_assoc ..

lemma into_star (a: Loc G 1)(m k:ℕ)(hs:0<σ)(hp:0≤η)(hc:0≤C):∃ K:ℝ,0≤K ∧ ∀ L:Side, Odd L.val→Threshold σ η m L→∀ S:Cross L (Loc G 1) (Loc G 1), gauss S η C k→ ∀ x:Site L,∀ T: Tile (edgeL G) m,∀ B:ℝ, Knoxville (fame _) σ (0,a) T B→ Knoxville (fame _) η (0,a) (upmost L x S T) (K*B):= by
    obtain ⟨X,Y,hX,hY,H⟩:=thorn_cost a m 0 hs hp hc
    refine ⟨X,hX,fun L ho hu S hS x T B h=>?_⟩; apply Knoxville.mono (H L ho hu S (fun i hi=> hS i (by omega)) x T 0 B h le_rfl (fun i j hj=>by rw [trim_nil] at hj; simp at hj))
    simp only [zero_mul,add_zero]; exact mul_le_of_le_one_right (mul_nonneg hX h.1) (ebb ..)
-- qualitative to polynomial price future
lemma terrace (F:Frame G d)(H:Hol G)(o:Loc G 1)(m u D e q:ℕ)(hq:q≤d+1)(σ η θ C:ℝ)(hθ:0<θ)(hp:θ≤σ)(he:0≤η)(hc:0≤C): ∃ X Y:ℝ,0≤X ∧ 0≤Y ∧ ∀ T:Anthem D G, Clef o T u → ∀ L:Side,Odd L.val → Threshold σ η m L→∀ S:Cross L (Loc G 1) (Loc G 1), gauss S η C q→∀ A C':ℝ, Bonds F o θ q e m T A → (∀ p : Studio D, Knoxville (fame _) σ (0,o) (T p e m) (C' * ‖p‖)) → 0≤C' → ∀ x:Site L,∀ f:Studio D,∀ k: Spring D, upper k.val<q → ∀ hL:2≤L.val,
   Knoxville (fame _) η (0,o) (upmost L x S (T ((notch k.val (paper_fits k) (throughW x D hL f)) • cone D k.val) e m)) ((X*C'* Dawn.scale L ^ q + Y*A) *‖f‖):= by
   choose c y hC hy Hy using fun i:Spring D=> north_bill H F o m u D e q hq i.val σ η θ C hθ hp he hc
   let n (i:Spring D):= ‖cone D i.val‖; let X:= ∑ i,c i*n i; let Y:=∑ i,y i
   have hm i:0≤ c i*n i:=mul_nonneg (hC i) (norm_nonneg _); have hX : 0≤X:= Finset.sum_nonneg (fun i _=>hm i); have hY : 0≤Y:=Finset.sum_nonneg fun i _=>hy i
   refine ⟨X,Y,hX,hY,fun T h L hu hw S hS A C' hA hr hP x f k hk hL=>?_⟩
   have hT: S.strip η C:= strip_mono (hS [] (Nat.zero_le q)) le_rfl (mul_le_of_le_one_right hc (ebb ..)); let V (p:Studio D):= upmost L x S (T p e m);let g:=notch k.val (paper_fits k) (throughW x D hL f)
   let d:=Dawn.scale L; let k':=upper k.val; let j:=m+(q-m-upper k.val)
   have hv:=Hy k T h _ hw hu _ (fun i hi=>hS i (le_trans hi (by omega))) _ hA _ (hr _) x
   have hh:V (g • cone D k.val)=g • V (cone D k.val) := (solas T h x hT hc he e m).map_smul ..
   rw [show upmost L x S _= _ from hh]; apply (hv.smul g).mono
   have he : |g|≤ d^k' * ‖f‖:= notch_down ..
   have H1 : c k*n k ≤ X:= Finset.single_le_sum (fun i _=>hm i) (Finset.mem_univ _)
   have H2 : y k≤Y:= Finset.single_le_sum (f:=y) (fun i _=>hy i) (Finset.mem_univ _)
   refine le_trans (mul_le_mul_of_nonneg_right he hv.1) ?_
   let W:=c k*(C'*n k); change d^_*‖f‖*(W*d^j + y k*A)≤ _
   have hD:0≤d:= Dawn.scale_pos.le; have hx:0≤W:=mul_nonneg (hC k) (mul_nonneg hP (norm_nonneg _))
   rw [mul_right_comm (d^k'),mul_add,mul_left_comm _ W, ← pow_add]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _);apply add_le_add
   · refine mul_le_mul ?_ (pow_le_pow_of_le_one hD Dawn.scale_small (show q≤ k'+j by unfold k' j;omega)) (pow_nonneg hD _) (mul_nonneg hX hP); unfold W; rw [mul_left_comm]; rw [mul_comm X]; exact mul_le_mul_of_nonneg_left H1 hP
   rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right ((mul_le_of_le_one_left (hy k) (pow_le_one₀ hD Dawn.scale_small)).trans H2) hA.1
end YM.FormalBulk08.Grail
