import YM.MS.Port.Hues
/-!
# Cultural ∫ Past clears. Identify multi Port from unique mark recursion. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Port
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo Vane
open Osc Fiddle Snap Book.Convolve Alps Arts City
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{K L:Planet G I}{F H:Glade G I}{U:Calculator G I}{x t:ℝ}(σ:I→ℝ)(u:ℤ)
lemma gain_pre (x t:ℝ): (· + - t) ⁻¹' Set.Iic (x-t)= Set.Iic x:= by ext; simp [sub_eq_add_neg]
lemma ahead (h:Job.train false F) : Job.train false (twist u σ F):= by
    intro i t w hc; let f x:= F i x ( sr (σ i) w ); obtain hp : IntegrableOn f ( Set.Iic ( t-σ i ) ):= h i _ _ (fun x=>Bool.noConfusion x); obtain he := (measurePreserving_add_right volume (-σ i) |>.integrableOn_comp_preimage ( Homeomorph.addRight (-σ i)|>.measurableEmbedding )).2 hp; rw [ gain_pre ] at he; change IntegrableOn (fun s=> τ _ _ * f ( s-σ i )) _ _; refine Integrable.const_mul ?_ _; simpa only [sub_eq_add_neg, IntegrableOn] using! he
lemma pipeS : river (twist u σ F) = twist u σ (river F):= by
    ext i t w; change (∫ r in Set.Iic t, τ _ _ * F i (r- σ i) _) = _; rw [integral_const_mul]; congr 1; -- shift unfold? right.C
    obtain hp:= (measurePreserving_add_right volume (-σ i) |>.setIntegral_preimage_emb ( Homeomorph.addRight (-σ i)|>.measurableEmbedding ) (fun s=>F i s (sr (σ i) w)) (Set.Iic ( t-σ i ))); rw [gain_pre] at hp; exact hp
lemma pack (h:collect F): collect (twist u σ F):= by obtain ⟨k,hk⟩:=h; refine ⟨ k,fun i t l hl=>?_⟩; change τ _ _ * _=0; rw [hk, mul_zero]; simp [sr]; omega
-- editing
variable {W:Type}[LinearOrder W]
def moved (σ:I→ℝ)(x:Position W I): Position W I:= fun w i=> exp ( σ i ) • x w i
abbrev glide (U:Site G I)(σ:I→ℝ)(t:ℤ) := fun n:ℕ=> twist t σ ( U n )
variable (J:W→ℕ)(Y: Position W I){B:Site G I}{X:Rake.Dance G I W}{A:W→ Site G I} (S:Finset W)(k:ℕ)
local notation "m0"=> (fun (_:I)=>planeF)
def loom (X: Rake.Dance G I W): Rake.Dance G I W:= fun S=>glide (X S) σ (charge J S)
lemma moving {Z:Finset W}(h:S.Nonempty)(_hx: Z.Nonempty)(i:I): rootX ( moved σ Y ) S i= exp (σ i) • rootX Y S i:= by rw [ rootX,rootX, dif_pos h,dif_pos h ]; rfl -- remove Z
lemma town : Src (moved σ Y) m0 (Θ0 G I) (Θ0 G I) (glide B σ 4) (loom σ J X) S k= twist ( ( charge J S ):ℤ ) σ ( Src Y m0 (Θ0 G I) (Θ0 G I) B X S k ):= by
    unfold Src multi lonely glide loom; rw [map_add]; simp_rw [map_sum]; refine congr_arg₂ (·+·) ?_ ?_
    · refine Finset.sum_congr rfl fun i hi=>?_ ; rw [expT, show ( (4:ℤ) + ( charge J S:ℤ )-4)=(charge J S:ℤ) from by omega]
    refine Finset.sum_congr rfl fun i hi=> Finset.sum_congr rfl fun j hj=> ?_; obtain ⟨hV,hT,hQ,h⟩:= n_small hi; have hp:S.Nonempty:= hT.mono hV.le; rw [ show rootX (moved σ Y) i-rootX (moved σ Y) S= (fun p=> exp (σ p) • ( rootX Y i-rootX Y S ) p) from funext (fun p=> (by simp only [Pi.sub_apply,moving σ Y i hT hp, moving σ Y S hp hp, smul_sub])), levelW ]; rw [ ← Nat.cast_add,toll_charge J hV.le]
lemma steer (H:Fields Y m0 (Θ0 G I) (Θ0 G I) B A X): Fields (moved σ Y) m0 (Θ0 G I) (Θ0 G I) (glide B σ 4) (fun i=>glide (A i) σ (J i)) (loom σ J X):= by
    refine ⟨?_,fun i=> ?_,fun S h k=>?_⟩; · unfold loom; rw [H.1]; exact funext fun i=> map_zero _
    · rw [ loom,H.2.1, charge, Finset.sum_singleton]
    obtain ⟨he,hV,hF⟩:= H.2.2 S h k; refine ⟨ pack σ _ he,?_⟩ -- result.S.arc
    let U:=loom σ J X; let Y':=glide B σ 4; let u:ℤ:=( charge J S ); let v:=sailP m0 (Θ0 G I); let F:=v ( U S k ) + Src ( moved σ Y ) m0 (Θ0 G I) (Θ0 G I) Y' U S k; let H:=v (X S k) + Src Y m0 (Θ0 G I) (Θ0 G I) B X S k; have hm:F=twist u σ H:= by
        unfold F H U Y'; rw [ map_add, town ]; apply congr_arg₂ (·+·) _ rfl; exact CycleT (Z:=I) u σ -- order?
    change Job.train false F ∧ twist u σ (X S k)= river F; rw [hm, pipeS]; exact ⟨ ahead σ u hV,congr_arg (twist u σ) hF⟩
end YM.MS.Port
