import YM.FormalBulk08.Palm.Pits

/-! Uniform application of the polynomial cancellations using homogeneous
prism norm from Flight. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Palm
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {I :Type*}{G:Gauge} {d m e l n D s j t:ℕ}{σ η A B:ℝ}{a:Loc G 1}{L:Side}

def billPr (G:Gauge)(n:ℕ)(u: Cover): Prism G.Color n→ₗ[ℝ](edgeL G→ℝ) where
    toFun x:= assigns (eastern (charted x) u)
    map_add' x y:= by rw [exposure_add]; rfl
    map_smul' t x:= by
       rw [show charted (t • x)= t • charted x from ?h]; rfl
       unfold charted; rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=>rfl
lemma peer_role {Y: Anthem D G}(o:Loc G 1) (U : Fin m→edgeL G→ℝ)(h:Clef o Y l)(he:∀ i,Stipend (U i)) : IsLinearMap ℝ (fun p:Studio D=>tariffs U (Y p e m)):= by
    obtain ⟨s,C,hs,-,H⟩:=h.fare.2.2 e m; obtain ⟨Z,hZ,Hz⟩:=pays_product U o hs he; refine ⟨fun p q=>?_,fun c p=>?_⟩
    · rw [h.map_add]; unfold tariffs; simp_rw [Pi.add_apply,add_mul]; exact Summable.tsum_add (Hz _ _ (H p)|>.1) (Hz _ _ (H q)|>.1)
    rw [h.map_smul]; unfold tariffs; simp only [Pi.smul_apply, smul_eq_mul,←tsum_mul_left]; exact tsum_congr fun v=>mul_assoc ..
lemma pristine (o: Loc G 1)(F: Frame G d)(u:Cover)(D q m l e:ℕ)(hq:q≤d+1)(v: Seasons)(r:Fin m→ℕ)(H:Hol G)(hr:∀ i,0<r i)
    (hv:(∑ i,r i)+ upper v <q) (hs:0<η) (A:Fin m→ℝ)(hA:∀ i,0≤A i) :
    ∃ C:ℝ,0≤C ∧ ∀ Y:Anthem D G,Clef o Y l→∀ B, Bonds F o η q e m Y B → ∀ W, Knoxville (fame _) η (0,o) (Y (cone D v) e m) W →∀ p: (i:Fin m)→Prism G.Color (r i), (∀ i,‖p i‖≤ A i) → ‖tariffs (fun i=> billPr G _ u (p i)) (Y (cone D v) e m)‖ ≤ C*B:= by
    let U i := billPr G (r i) u; let P i:= Prism G.Color (r i)
    let b (i:Fin m):= Module.finBasis ℝ (P i); let I (i:Fin m):= Fin (Module.finrank ℝ (P i))
    let Z i (a:I i):=eastern (charted (b i a)) u; have hb i j:Z i j ∈ rangeLt (Axis→G.Color) (r i):= band_shift (read_poly _) _
    choose! C hC HC using fun w:(i:Fin m)→ I i => hypotheses o F e q m hq v D l (fun i=>Z i (w i)) r hr hv (fun i=>hb _ _) H hs
    let k i (a:I i):=LinearMap.toContinuousLinearMap ((b i).coord a); let c i j:= ‖k i j‖*A i; let M (w:(i:Fin m)→I i):= ∏ i,c i (w i); have hM w:0≤M w:= Finset.prod_nonneg (fun i _=>mul_nonneg (norm_nonneg (k i (w i))) (hA _))
    refine ⟨∑ i,M i*C i,Finset.sum_nonneg (fun i _=> mul_nonneg (hM i) (hC i)),fun Y ht hv hF W hw p hp=>?_⟩; let t:=Y (cone D v) e m
    let T i j:= assigns (Z i j); let D i j:=k i j (p i) • T i j
    rw [show (fun i : Fin m=> (billPr _ _ _ (p i)))= fun i=>∑ j:I i,D i j from ?h, dial D ?hy hs t hw,Finset.sum_mul]; apply (norm_sum_le ..).trans; refine Finset.sum_le_sum fun i _=>?_
    · have he : tariffs (fun j=>D j (i j)) t= (∏ j:Fin m,k j (i j) (p j))* tariffs (fun j=>T j (i j)) t:= by unfold tariffs; rw [←tsum_mul_left]; refine tsum_congr fun u=>?_; unfold D; simp only [Pi.smul_apply,smul_eq_mul,Finset.prod_mul_distrib]; rw [mul_left_comm]
      rw [he,_root_.norm_mul,norm_prod, mul_assoc];exact mul_le_mul (Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun j _=> ((k j (i j)).le_opNorm (p j)).trans (mul_le_mul_of_nonneg_left (hp j) (norm_nonneg (k j (i j)))))) (HC i Y ht _ hF _ hw) (norm_nonneg _) (hM i)
    case h=> funext i; nth_rw 1 [← (b i).sum_repr (p i)]; rw [map_sum]; apply Finset.sum_congr rfl; intro j _; rw [map_smul];rfl
    case hy=> exact fun i j=>shoulder (Submodule.smul_mem (rangeLt (Axis→G.Color) (r i)) (k i j (p i)) (hb i j))

lemma reel_norm {q p: Prism G.Color n} {U:Side}{X: Carrier.Lines U}{C:ℝ} (hX: Reel X q p C)(h:0≤C) : ‖p‖≤ C * pile q := by
   have hh: 0≤ C*pile q:= mul_nonneg h (pile_pos q); exact (pi_norm_le_iff_of_nonneg hh).2 fun i=> (hX.pay i).trans (mul_le_of_le_one_right hh (pow_le_one₀ (unitStep_pos _).le (unitStep_le _)))
end YM.FormalBulk08.Palm
