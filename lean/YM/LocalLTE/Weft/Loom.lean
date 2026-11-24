import YM.LocalLTE.Weft.Triangle
/-! Capsules: coefficient reproduction in a common chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Weft
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Mask Matter Coat Frond
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Fan Brush Foramen Pastel
variable {v z r C w s t y η γ B a ε α κ K: ℝ} {j n m k N M : ℕ}
open Weft AnalyticBridge.VerifiedReset FrameBox Tensor
local notation "E"=> Directions G c
namespace Scene
variable (j:ℕ) {o:Site c} (X:Grove o)
lemma sphere (P:Cabana.Pkt (Directions G c) j)(u:ℝ)(i) : ‖u • FrameBox.colorP P i‖≤‖u • P i‖:=by
    unfold colorP; rw [←MeasureTheory.integral_smul]; apply (norm_integral_le_integral_norm ..).trans
    let T v:= FrameBox.castP P i v; let C' x:= u • T x; have hv: Continuous C' := (FrameBox.cast_cont P i).const_smul u
    refine (MeasureTheory.integral_mono (f:=fun x=> ‖C' x‖) (g:=fun _=> ‖u • P i‖) ((hv.norm).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (integrable_const _) (fun x=>?_)).trans_eq (by simp)
    unfold C'; dsimp only; rw [norm_smul,norm_smul]; refine mul_le_mul_of_nonneg_left (_root_.le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le (P i) (fun _=>FrameBox.wheel x)) (?_)) (norm_nonneg _); simp only [prod_const,card_univ,Fintype.card_fin]; exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=>by rw [one_mul]; exact FrameBox.wheel_norm ..))
lemma spinner {κ:ℝ}(n m:ℕ){g:ℝ→E→ℝ} (h: Arp k j C g)(he:n≤j) : Scene X κ m k n (fun s=> realise X m κ (colorP (fun i:Fin n=> Tensor.coeff (g s) i 0))) C:=by
    let p(s:ℝ)(i:Fin n):=Tensor.coeff (g s) i 0
    have hK : Hex k p:=by
       choose f hf using (fun i:Fin n=> h.coeffHex i.val (i.isLt.le.trans he)); exact ⟨fun i j=> f j i, fun s hs=> funext fun i=> (hf i s hs).trans (by rw [Finset.sum_apply]; rfl)⟩ -- pi dep
    let L:Cabana.Pkt E n→ₗ[ℝ] (Config G c→ℝ):= PhysicalNext.Repeat.East.linearO X m κ (1,0) 1 -- edit; easier standalone
    refine ⟨h.nonneg,?_,fun s hs=> ⟨_,rfl,fun i=> (sphere n (p s) _ i).trans (h.postage i.val (i.isLt.le.trans he) s hs)⟩⟩
    exact (hK.alpha L).change fun i hi=> funext fun x=>by change 1*realise X m κ (colorP (p i)) (pull 1 0 x)=_; rw [Lattice.pull_id,one_mul]
-- stable norms shape registration
variable {j}
lemma generous {f:ℝ→ Config G c→ℝ} (h:Scene X κ N j n f C)(hk : j ≤ k)(he:C≤v): Scene X κ N k n f v:=
  ⟨h.price.trans he,h.weft.grow hk, fun i hi=> by obtain ⟨p,hp,hz⟩:= h.plaque i hi; exact ⟨p,hp,fun i=> (hz i).trans he⟩⟩
lemma change {f g:ℝ→ Config G c→ℝ} (h:Scene X κ N j n f C)(he:Set.EqOn f g clip):Scene X κ N j n g C:= ⟨h.price,h.weft.change he,fun i hi=> he hi ▸ h.plaque i hi⟩
lemma scale {f:ℝ→ Config G c→ℝ}(h:Scene X κ N j n f C) (s:ℝ): Scene X κ N j n (fun u=> s • f u) (|s| *C):=by
   refine ⟨mul_nonneg (abs_nonneg _) h.price,h.weft.oneZ _,fun u hu=>?_⟩; obtain ⟨p,hp,hP⟩:= h.plaque u hu; refine ⟨s • p,?_,fun i=>?_⟩
   · simp only [hp]; unfold FrameBox.realise; rw [Cabana.actual_smul]; rfl
   rw [Pi.smul_apply,smul_comm,norm_smul]; exact mul_le_mul_of_nonneg_left (hP _) (norm_nonneg _)
lemma blank (x : Grove o): Scene x κ N j n (fun _=> (0:Config G c→ℝ)) 0:= ⟨le_rfl,Hex.constant _,fun s hs=> ⟨0, by funext; simp [FrameBox.realise,Cabana.actual,Tensor.diagonal,Finset.sum_apply],by simp⟩⟩ -- edit
end Scene
end YM.LocalLTE.Weft
