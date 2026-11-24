import YM.FormalBulk08.Sable.Silo
/-! Coordinate feedthrough. Cancellations exact & blocked a priori.
Adaptation from Oath. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sable
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Grail Work.F03 Work.F05 Work.F08
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels Dawn
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{d m D u:ℕ}{σ η A C:ℝ}
lemma warrant (hz:(d+1)*(d+1) ≤ u) : d+1≤u:= (Nat.le_mul_of_pos_left (d+1) (Nat.succ_pos d)).trans hz
lemma rum (T:Anthem D G)(o:Loc G 1)(h: Clef o T m)(p e r):∃ B σ:ℝ,0<σ ∧ Knoxville (fame _) σ (0,o) (T p e r) B:= by obtain ⟨s,c,hs,hc,H⟩:=h.fare.2.2 e r;exact ⟨_,s,hs,H _⟩
lemma blizzard (H:Source.Hol G)(F:Labels.Frame G d)(o:Loc G 1)(m l D e q:ℕ)(hx:q≤d+1)(s: Seasons)(hz:(d+1)*(d+1)≤ u) :∃ C:ℝ,0≤C ∧∀ Y:Anthem D G,Clef o Y l→∀ A:ℝ,Steps F o u q e m Y A → ∀ i: chain (Loc G 1) m,∀ t∈ trimmed (Fin m×Axis) (q-m-upper s), ‖tariffs (fun j:Fin m=> assigns (horn (aster t j) (i j))) (Y (cone D s) e m)‖≤ C*A:= by
   let I:=chain (Loc G 1) m; let R:=trimmed (Fin m×Axis) (q-m-upper s)
   have hh(i:I)(t:↥R): ∃ C:ℝ,0≤C ∧ ∀ Y:Anthem D G,Clef o Y l→∀ B:ℝ,Steps F o u q e m Y B →‖tariffs (fun j=> assigns (horn (aster t.val j) (i j))) (Y (cone D s) e m)‖≤ C*B:= by
       have Hk : (∑ i:Fin m,(upper (aster t.val i)+1))+ upper s<q:= by
          rw [Finset.sum_add_distrib,←adder,Finset.sum_const, Finset.card_univ,Fintype.card_fin]; simp only [smul_eq_mul,mul_one]
          have hg:upper t.val<(q-m-upper s):=(trim_def ..).mp t.property; omega
       exact stitchK o F e q m hx s D l (fun j=>horn (aster t.val j) (i j)) (fun j=>upper (aster t.val j)+1) (fun j=>by omega) Hk (fun j=>horns _ _) H hz
   choose! C hC H using hh; let X(i:I):=∑ j,C i j; have hz i:0≤X i:=Finset.sum_nonneg (fun _ _=> hC i _); let Z:= ∑ i,X i
   refine ⟨Z,Finset.sum_nonneg (fun i _=> hz i),fun Y h A he i j hj=>?_⟩; apply (H i ⟨j,hj⟩ Y h A he).trans; exact mul_le_mul_of_nonneg_right ((Finset.single_le_sum (fun j _=> hC i j) (Finset.mem_univ _)).trans (show X i≤Z from Finset.single_le_sum (fun i _=>hz i) (Finset.mem_univ i))) he.1
lemma orbital (H:Source.Hol G)(F:Frame G d)(o:Loc G 1)(m l D e q:ℕ)(hx:q≤d+1)(s: Seasons)(hz:(d+1)*(d+1)≤u)(hs:0<η)(hc:0≤C): ∃ X Y:ℝ,0≤X ∧ 0≤Y ∧
   ∀ T: Anthem D G,Clef o T l→∀ L:Side,Odd L.val→∀ S:Cross L (Loc G 1) (Loc G 1), gauss S η C q →∀ A:ℝ, Steps F o u q e m T A→∀ B, Knoxville (grain (fame _) 1) u (0,o) (T (cone D s) e m) B→∀ x:Site L,
      Knoxville (grain (fame _) 1) u (0,o) (upmost L x S (T (cone D s) e m)) (X*B* Dawn.scale L ^ (m+(q-m-upper s))+Y*A):= by
   obtain ⟨X,E,hx',hE,HX⟩:=needle o m u (q-m-upper s) (by have := warrant hz; omega) hs hc; obtain ⟨V,hV,HV⟩:=blizzard H F o m l D e q hx s hz
   refine ⟨X,E*V,hx',mul_nonneg hE hV,fun T h L ho S hG A hb B hR x=>?_⟩
   apply Knoxville.mono (HX L ho S (fun i hi=>hG i (by omega)) x _ (rum T o h _ _ _) _ _ hR (mul_nonneg hV hb.1) (fun i t he=> HV T h _ hb i t he)); apply le_of_eq; change _=X*B* (L.val:ℝ)⁻¹^_+_;ring
lemma igloo (F:Frame G d)(H:Hol G)(o: Loc G 1)(m l D e q:ℕ)(hq:q≤d+1)(hp:(d+1)*(d+1)≤u)(hs:0<η)(hc:0≤C):∃ X Y:ℝ,0≤X∧0≤Y∧∀ T: Anthem D G,Clef o T l→∀ L:Side,Odd L.val → ∀ S:Cross L (Loc G 1) (Loc G 1),gauss S η C q→ ∀ A C':ℝ,Steps F o u q e m T A →(∀ p: Studio D, Knoxville (grain (fame _) 1) u (0,o) (T p e m) (C'*‖p‖))→ 0≤C' →∀ x:Site L,∀ f:Studio D,∀ k:Spring D, upper k.val<q →∀ hL:2≤L.val,
   Knoxville (grain (fame _) 1) u (0,o) (upmost L x S (T ((notch k.val (paper_fits k) (throughW x D hL f)) • cone D k.val) e m)) ((X*C'* Dawn.scale L ^ q + Y*A) *‖f‖):= by
   choose c y hC hy Hy using fun i: Spring D=> orbital H F o m l D e q hq i.val hp hs hc
   let n (i:Spring D):= ‖cone D i.val‖; let X:= ∑ i,c i*n i; let Y:=∑ i,y i
   have hm i:0≤c i*n i:=mul_nonneg (hC i) (norm_nonneg _);have hX : 0≤X:= Finset.sum_nonneg (fun i _=>hm i); have hY:0≤Y:=Finset.sum_nonneg fun i _=>hy i
   refine ⟨X,Y,hX,hY,fun T h L hu S hS A C' hA hr hP x f k hk hL=>?_⟩
   have hT:S.strip η C:= strip_mono (hS [] (Nat.zero_le q)) le_rfl (mul_le_of_le_one_right hc (ebb ..));let V(p:Studio D):=upmost L x S (T p e m);let g:=notch k.val (paper_fits k) (throughW x D hL f)
   let d:=Dawn.scale L; let k':=upper k.val; let j:=m+(q-m-upper k.val)
   have hv:=Hy k T h _ hu _ hS _ hA _ (hr _) x
   have hh:V (g • cone D k.val)=g • V (cone D k.val):= (solas T h x hT hc hs.le e m).map_smul ..
   rw [show upmost L x S _= _ from hh]; apply (hv.smul g).mono
   have he : |g| ≤ d^k'* ‖f‖:= notch_down ..; have H1 : c k*n k≤X:= Finset.single_le_sum (fun i _=>hm i) (Finset.mem_univ _); have H2 : y k≤Y:= Finset.single_le_sum (f:=y) (fun i _=>hy i) (Finset.mem_univ k)
   refine le_trans (mul_le_mul_of_nonneg_right he hv.1) ?_
   let W:=c k*(C'*n k); change d^_*‖f‖*(W*d^j+y k*A)≤_
   have hD: 0≤d:= Dawn.scale_pos.le; have hx:0≤ W:=mul_nonneg (hC k) (mul_nonneg hP (norm_nonneg _));rw [mul_right_comm (d^k'),mul_add,mul_left_comm _ W,←pow_add]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _);apply add_le_add
   · refine mul_le_mul ?_ (pow_le_pow_of_le_one hD Dawn.scale_small (show q≤ k'+j by unfold k' j;omega)) (pow_nonneg hD _) (mul_nonneg hX hP); unfold W; rw [mul_left_comm]; rw [mul_comm X]; exact mul_le_mul_of_nonneg_left H1 hP
   rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right ((mul_le_of_le_one_left (hy k) (pow_le_one₀ hD Dawn.scale_small)).trans H2) hA.1
lemma skates (F:Frame G d)(H:Hol G)(a:Loc G 1)(m l D e q:ℕ)(hq:q≤d+1)(hp:(d+1)*(d+1)≤u)(hD:d+1≤D)(hs:0<η)(hc:0≤C): ∃ X Y:ℝ,0≤X ∧ 0≤Y∧∀ T: Anthem D G, Clef a T l → ∀ L:Side,Odd L.val → ∀ S:Cross L (Loc G 1) (Loc G 1),gauss S η C q →∀ A C':ℝ, Steps F a u q e m T A → (∀ p, Knoxville (grain (fame _) 1) u (0,a) (T p e m) (C'*‖p‖)) → 0 ≤ C' → ∀ x:Site L,∀ hL:2 ≤ L.val, ∀ f:Studio D,
    Knoxville (grain (fame _) 1) u (0,a) (upmost L x S (T (throughW x D hL f) e m)) ((X*C'*Dawn.scale L^q+Y*A)*‖f‖):= by
    let n:ℝ:=q; let M:ℝ:= Fintype.card (Spring D)
    obtain ⟨X,Y,hX,hY,Hq⟩:= igloo F H a m l D e q hq hp hs hc; obtain ⟨Z,W,hZ,hW,HZ⟩:= needle a m u 0 (Nat.zero_le _) hs hc
    have hn:0≤n:= Nat.cast_nonneg _; have hM:0≤M:= Nat.cast_nonneg _
    refine ⟨n*M*X+ Z*32^q,n*M*Y,by positivity,by positivity,fun T h L ho S hu A B hA hb hB x hL f=>?_⟩
    let V (p:Studio D):= upmost L x S (T p e m); have hV:IsLinearMap ℝ V:=solas T h x (show S.strip η C from strip_mono (hu [] (Nat.zero_le _)) le_rfl (mul_le_of_le_one_right hc (ebb ..))) hc hs.le _ _
    let U:=throughW x D hL f; let g:=∑ i∈ Finset.range q,pamphlet U i
    have h1: Knoxville (grain (fame _) 1) u (0,a) (V (U-g)) (Z*(B* (32^q*(Dawn.scale L^q* ‖f‖)))):= by
        have hx:=HZ L ho S (fun i hi=> hu i (by omega)) x (T (U-g) e m) (rum T a h (U-g) _ _) 0 _ (hb _) le_rfl (fun i j hj=>by rw [trim_nil] at hj;simp at hj);apply hx.mono;rw [zero_mul,add_zero];exact (mul_le_of_le_one_right (mul_nonneg hZ (mul_nonneg hB (norm_nonneg _))) (ebb ..)).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (earns x f q (hq.trans hD) hL) hB) hZ)
    let X':=(X*B*Dawn.scale L^q+Y*A)*‖f‖; let fV:Studio D→ₗ[ℝ]Tile (edgeL G) m:=⟨⟨V,hV.1⟩,hV.2⟩
    have h2: Knoxville (grain (fame _) 1) u (0,a) (V g) (n*(M*X')):=by
       change Knoxville (grain (fame _) 1) u (0,a) (fV g) _; unfold g; rw [map_sum]; have heq (j)(hj:j∈Finset.range q): Knoxville (grain (fame _) 1) u (0,a) (fV (pamphlet U j)) (M*X'):= by
          unfold pamphlet; rw [map_sum]; have ha:=hA.1; have ht':0≤ Dawn.scale L:= Dawn.scale_pos.le; refine Knoxville.mono (knox_sum (peers D j) (T:=fun i=>fV (notch i.val (paper_fits i) U • cone D i.val)) (fun i hi=>?_)) (cardinal _ (X') (by unfold X'; positivity))
          exact Hq T h L ho S hu A B hA hb hB x f i (((Finset.mem_filter.mp hi).2).trans_lt (Finset.mem_range.mp hj)) hL
       apply (knox_sum (Finset.range q) heq).mono; rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    change Knoxville _ _ _ (V U) _;rw [show V U=V (U-g)+V g from (by rw [←hV.1,sub_add_cancel])]; apply (h1.add h2).mono; apply le_of_eq; unfold X';ring
lemma slol (F:Frame G d)(H:Hol G)(a:Loc G 1)(m l D e q:ℕ)(hq:q≤d+1)(hp:(d+1)*(d+1)≤u)(hD:d+1≤D)(hs:0<η)(hc:0≤C): ∃ X Y:ℝ,0≤X ∧ 0≤Y ∧ ∀ T:Anthem D G,Clef a T l →∀ L:Side,Odd L.val →∀ S:Cross L (Loc G 1) (Loc G 1),gauss S η C q→∀ A C':ℝ,Steps F a u q e m T A → (∀ p,Knoxville (grain (fame _) 1) u (0,a) (T p e m) (C'*‖p‖)) → 0≤C' →∀ hL:2≤L.val,∀ f, Knoxville (grain (fame _) 1) u (0,a) (towerV S T d e m hL f) ((heightK L d q*X*C'+(L.val:ℝ)^d* Y*A)*‖f‖):= by
   obtain ⟨X,Y,hX,hY,H⟩:=skates F H a m l D e q hq hp hD hs hc; refine ⟨_,_,hX,hY,fun T ht L ho S Hs A C' ha hz hC hL f=>?_⟩; apply ((knox_sum Finset.univ (fun i _=> H T ht L ho S Hs A C' ha hz hC i hL f)).smul (aven L d)).mono; rw [income_by]; apply le_of_eq; unfold heightK;ring
end YM.FormalBulk08.Sable
