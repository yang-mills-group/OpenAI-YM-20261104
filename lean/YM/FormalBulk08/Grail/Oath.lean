import YM.FormalBulk08.Grail.Summer

/-! All of U_same and section scaling powers (pre-L). -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Grail
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{m d D e j t :ℕ}{A B C U η σ θ:ℝ}{a:Loc G 1}{L:Side}{K:KernelChoices}

lemma cardinal (i:ℕ)(B:ℝ)(h:0≤B):∑ _∈Dawn.peers D i,B ≤ Fintype.card (Spring D)*B:= by simp only [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_univ _)) h
lemma overcast (H:Hol G)(F:Frame G d)(a:Loc G 1)(m u D e q:ℕ)(hq:q≤d+1)(hD:d+1≤D)(σ η θ C:ℝ)(hθ:0<θ)(hp:θ≤σ)(he:0≤η)(hc:0≤C): ∃ X Y:ℝ,0≤X ∧ 0≤Y ∧ ∀ T:Anthem D G, Clef a T u → ∀ L:Side,Odd L.val → Threshold σ η m L→∀ S:Cross L (Loc G 1) (Loc G 1), gauss S η C q→∀ A C':ℝ,Bonds F a θ q e m T A → (∀ p, Knoxville (fame _) σ (0,a) (T p e m) (C'*‖p‖)) → 0≤C' → ∀ x:Site L,∀ hL:2 ≤L.val, ∀ f:Studio D,
    Knoxville (fame _) η (0,a) (upmost L x S (T (throughW x D hL f) e m)) ((X*C'*Dawn.scale L^q + Y*A)*‖f‖):= by
    let n:ℝ:=q; let M:ℝ:= Fintype.card (Spring D)
    obtain ⟨X,Y,hX,hY,Hq⟩:= terrace F H a m u D e q hq σ η θ C hθ hp he hc; obtain ⟨Z,hZ,HZ⟩:= into_star a m q (lt_of_lt_of_le hθ hp) he hc
    have hn : 0≤ n:= Nat.cast_nonneg _; have hM:0≤M:=Nat.cast_nonneg _
    refine ⟨n*M*X + Z*32^q,n*M*Y,by positivity,by positivity,fun T hv L ho ht S hu A B hA hb hB x hL f=>?_⟩
    let V (p:Studio D):= upmost L x S (T p e m); have hV:IsLinearMap ℝ V:= solas T hv x (show S.strip η C from strip_mono (hu [] (Nat.zero_le _)) le_rfl (mul_le_of_le_one_right hc (ebb ..))) hc he _ _
    let U:=throughW x D hL f
    let g:=∑ i∈ Finset.range q,pamphlet U i
    have h1 : Knoxville (fame _) η (0,a) (V (U-g)) (Z*(B* (32^q*(Dawn.scale L^q* ‖f‖)))):=
       (HZ L ho ht S hu x _ _ (hb _)).mono (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (earns x f q (hq.trans hD) hL) hB) hZ)
    let X':=(X*B*Dawn.scale L^q+Y*A)*‖f‖
    let fV:Studio D→ₗ[ℝ]Tile (edgeL G) m:=⟨⟨V,hV.1⟩,hV.2⟩ -- code
    have h2 : Knoxville (fame _) η (0,a) (V g) (n*(M*X')):= by
       change Knoxville (fame _) η (0,a) (fV g) _; unfold g; rw [map_sum]; have heq (j)(hj:j∈Finset.range q): Knoxville (fame _) η (0,a) (fV (pamphlet U j)) (M*X'):= by
          unfold pamphlet; rw [map_sum]; have ha:=hA.1; have ht':0≤ Dawn.scale L:= Dawn.scale_pos.le; refine Knoxville.mono (knox_sum (peers D j) (T:=fun i=>fV (notch i.val (paper_fits i) U • cone D i.val)) (fun i hi=>?_)) (cardinal _ (X') (by unfold X'; positivity))
          exact Hq T hv L ho ht S hu A B hA hb hB x f i (((Finset.mem_filter.mp hi).2).trans_lt (Finset.mem_range.mp hj)) hL
       apply (knox_sum (Finset.range q) heq).mono; rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    change Knoxville _ _ _ (V U) _; rw [show V U=V (U-g)+V g from (by rw [←hV.1,sub_add_cancel])]; apply (h1.add h2).mono; apply le_of_eq; unfold X'; ring

-- economic factor L^d.
def heightK (L:Side) (d q : ℕ):ℝ:=(L.val:ℝ)^d * Dawn.scale L ^q
lemma tall_zero (L:Side): heightK L d (d+1)= Dawn.scale L:= by unfold heightK Dawn.scale; rw [pow_succ,inv_pow]; field_simp
lemma heightK_of_le {k:ℕ}(L:Side)(hd:k≤d): heightK L d k=(L.val:ℝ)^(d-k):= by unfold heightK Dawn.scale;rw [inv_pow]; nth_rw 1 [show d=d-k+k by omega,pow_add,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ (by positivity)),mul_one];

def towerV (S:Cross L (Loc G 1) (Loc G 1))(T: Anthem D G)(d : ℕ)(e r:ℕ)(hL:2≤L.val)(v:Dawn.Studio D):= aven L d • ∑ x: Site L, upmost L x S (T (throughW x D hL v) e r)
def blade (P:Flight j t)(K:KernelChoices)(V:Lodge P.patch)(T: Anthem D G)(d e r:ℕ)(hL:2≤P.L.val)(v:Studio D):= aven P.L d • ∑ x:Site P.L, lowmost P K V x (T (throughW x D hL v) e r)
lemma income_by (L:Side)(X:ℝ)(d): |aven L d| * ∑ _:Site L,X=(L.val:ℝ)^d*X:= by rw [abs_of_pos (aven_pos ..),aven,Finset.sum_const,nsmul_eq_mul, Finset.card_univ]; field_simp

lemma oath (H:Hol G)(F:Frame G d)(a:Loc G 1)(m u D e q:ℕ)(hq:q≤d+1)(hD:d+1≤D)(σ η θ C:ℝ)(hθ:0<θ)(hp:θ≤σ)(he:0≤η)(hc:0≤C): ∃ X Y:ℝ,0≤X ∧ 0≤Y ∧ ∀ T:Anthem D G, Clef a T u → ∀ L:Side,Odd L.val → Threshold σ η m L→∀ S:Cross L (Loc G 1) (Loc G 1), gauss S η C q→∀ A C':ℝ,Bonds F a θ q e m T A → (∀ p, Knoxville (fame _) σ (0,a) (T p e m) (C'*‖p‖)) → 0≤C' → ∀ hL:2≤L.val,∀ f, Knoxville (fame _) η (0,a) (towerV S T d e m hL f) ((heightK L d q * X*C' + (L.val:ℝ)^d*Y*A)*‖f‖):= by
   obtain ⟨X,Y,hX,hY,H⟩:= overcast H F a m u D e q hq hD σ η θ C hθ hp he hc
   refine ⟨_,_,hX,hY,fun T ht L ho hW S hs A C' ha hz hC hL f=>?_⟩; apply ((knox_sum Finset.univ (fun i _=> H T ht L ho hW S hs A C' ha hz hC i hL f)).smul (aven L d)).mono; rw [income_by]; apply le_of_eq; unfold heightK; ring

lemma tollgate (a:Loc G 1)(P: Flight j t)(V:Lodge P.patch)(d e r:ℕ)(K:KernelChoices)(T:Anthem D G)(u:ℕ)(ht: Clef a T u)(S C Z:ℝ)(he:(Flight.duo K.penalty P).A0.strip η S)(hc:0≤S)(hz:(locating G K P V).strip η C)(hZ:(roots G K P V).strip η Z)(hs:0<η)(hp:η≤P.L.val * θ)(hh:0≤θ){A B:ℝ}(hb:0≤B)(hx:∀ v, Knoxville (fame _) θ (0,a) (T v e r) (A * ‖v‖))(hu:∀ v,Torrid (T v e r) θ (B*‖v‖) a)(hL:2≤P.L.val):
    let X := (Fintype.card (Bank.Board G P.patch):ℝ)* (1 *(Fintype.card (BoardL G P.patch V)*(1*max 1 C)))
    let b:=max S (max Z X)
    ∀ f: Studio D, Knoxville (fame _) η (0,a) (blade P K V T d e r hL f-towerV (chair P G K) T d e r hL f) ((P.L.val:ℝ)^d*r*(Real.exp (8*η)*(Fintype.card (Loc G 1)*(b+b))^r)*B*‖f‖):= by
    intro X b f; unfold blade towerV; rw [←smul_sub,←Finset.sum_sub_distrib];let W:ℝ:=r*(Real.exp (8*η)*(Fintype.card (Loc G 1)*(b+b))^r)
    have hb': 0≤b := hc.trans (le_max_left ..); have hw:0≤W := by unfold W; positivity
    let g x:= throughW x D hL f
    have he' x: Knoxville (fame _) η (0,a) (lowmost P K V x (T (g x) e r)- upmost P.L x (chair P G K) (T (g x) e r)) (W*B*‖f‖):= by
       have hg:=uranic a P V x hs hp hh (hx (g x)) (ht.fare.2.1 (g x) _ _) (hu (g x)) he hc hz hZ
       apply hg.mono; refine le_trans (le_of_eq (b:= W*B*‖g x‖) ?_) (mul_le_mul_of_nonneg_left (Dawn.through_le x hL f) (mul_nonneg hw hb)); unfold W b X; dsimp; ring
    apply ((knox_sum Finset.univ (fun x _=>he' x)).smul _).mono; rw [income_by]; apply le_of_eq; unfold W; ring
end YM.FormalBulk08.Grail
