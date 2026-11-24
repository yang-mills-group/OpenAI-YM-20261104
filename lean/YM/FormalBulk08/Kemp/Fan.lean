import YM.FormalBulk08.Kemp.Birch

/-! Rite for W turn relative T, so think of full maps Y transformed
through their reference frames. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Kemp
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Bank
open Stationary Lotus Shore Mesa Gorge City Cork Rift Next.Free Flat RG Precision Tree
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {I J: Type*} {η θ A B C : ℝ} {l i u j t r D d : ℕ}{K: KernelChoices}

def Son (Y X: Anthem D G)(u:ℕ)(s:Signed):Prop :=∀ n p,Rite (banner u (Y p) n) (banner u (X (Dawn.froth s D p)) n) s 0

def Solo (Y:Anthem D G)(u:ℕ):=Son Y Y u 1
lemma solo_iff (Y:Anthem D G) : Solo Y u ↔ ∀ n p,Rite (banner u (Y p) n) (banner u (Y p) n) 1 0:= by unfold Solo Son; simp_rw [Dawn.froth_self]

variable (a:Loc G 1)(P:Flight j t)(V:Lodge P.patch)(Y X: Anthem D G)(W:Pot G)(ρ:ChartRatio G)(h:P.patch.Branches K G)
    (hp: Wade a Y u)(hv: Story W (pink K.penalty P.wing))(hr: LocalRatio ρ)(hL:2≤P.L.val)
    (ht:4≤t)(hx: Wade a X u)(k:(n:Side)→ (primary P.patch K n).Choices)(s:Signed) (Hz: Son Y X u s)

include hp hv hr ht hx Hz
lemma fan_rite (p:Dawn.Studio D)(d:ℕ)(n: Side) : Rite (quickP P V W Y ρ h hL d u p n (k n)) (quickP P V W X ρ h hL d u (Dawn.froth s D p) n (k n)) s 0:= by
    let S:=primary P.patch K n; let K':=k n; let Z:=stone W (n*P.patch.L)
    let U (T:Pot G) := tossed P ρ h V n K' Z (banner u T (n*P.patch.L)); let q:= Dawn.froth s D p; let Q b:= U (stepsong P X hL q b);let F b:=U (stepsong P Y hL p b)
    have he (b:Site P.L): Rite (F (s.act b)) (Q b) s 0:= by
       obtain ⟨t',C,h₀,hC,H,-⟩:= colors G K.penalty K.penalty_pos P.legal
       refine tossed_ward P ρ h V n K' Z (stoned_main h₀.le hC.le (H P.wing).1 hv.toVivid hv.ink _) hr ht (hv.civic _) s 0 _ _ ?_
       let m:=n*P.patch.L
       have h' (Z:Anthem D G) (hZ: Wade a Z u)(u' : Site P.L)(p:Dawn.Studio D) : banner u (stepsong P Z hL p u') m=resite (wrap m (lift u')) (banner u (Z (Dawn.throughW u' _ hL p)) m):= seated (lift u') _ u _ (hZ.1 _) (hZ.2.1 _)
       rw [h' Y hp,h' X hx]; unfold q; rw [Dawn.froth_inter _ _ P.odd, Ratio.lift_signed_of_odd P.odd,←wrap_signed, show S.ratio.embed 0 = 0 from ?_]
       · exact repulp _ s _ _ (Hz m _)
       rw [← Ratio.root_embed]; exact map_zero _
    intro I i a b t A B H H' hT hu hV
    let g:=roam ℝ (motor a); let f:=roam ℝ (motor b); unfold quickP; simp_rw [map_mul,map_sum,Wine.snow];
    apply congr_arg; symm; exact Fintype.sum_equiv s.actEquiv.toEquiv (fun b=> f (Q b)) (fun b=>g (F b)) (fun x=> (he x I a b t A B H H' hT hu hV).symm)

-- Gauge invariance of transformed Mark all grades.
omit k
lemma son_step (d:ℕ): Son (quick P V W Y ρ h hL d u) (quick P V W X ρ h hL d u) u s:= by
   intro n p; let k n:= Classical.choice (chooseable n (n*P.patch.L) (primary P.patch K n))
   let q:=Dawn.froth s D p
   let Y':=quick P V W Y ρ h hL d u;let X':=quick P V W X ρ h hL d u
   have hh: Wade a Y' u:=quick_Wade a P V Y W ρ h hp hv hr hL ht le_rfl d;have hH: Wade a X' u:=quick_Wade a P V X W ρ h hx hv hr hL ht le_rfl d
   let f n:=quickP P V W Y ρ h hL d u p n (k n);let g n:=quickP P V W X ρ h hL d u q n (k n)
   have hf (n): Young (rancho (f n)) u:= quickP_breeze a P V W Y ρ h hL hp hv hr le_rfl ht p n _
   have hg (n): Young (rancho (g n)) u:= quickP_breeze a P V W X ρ h hL hx hv hr le_rfl ht q n _
   refine verdict n s (P:=Y' p) (Q:=X' q) (x:=(0,a)) (y:=(0,a)) (fan_rite a P V Y X W ρ h hp hv hr hL ht hx k s Hz p d) (fun e=>u+e) (fun e=>u+e) (fun j=>.of_forall fun m i hi=>Classical.byContradiction (fun hv=> not_lt.mpr (hf _ j _ hv) hi)) (fun j=>.of_forall fun m i hi=>Classical.byContradiction (fun hv=> not_lt.mpr (hg _ j _ hv) hi)) ?_ ?_ (fun j r=> badge (Y' p) (hh.1 _) (hh.2.1 _) le_rfl n j r) (fun j r=>badge (X' q) (hH.1 _) (hH.2.1 _) le_rfl n j r)
   · intro j r; obtain ⟨x,hJ,H,-⟩:=brig a P V Y W ρ h hp hv hr hL ht (le_refl u) k j r d; exact ⟨x,hJ,H p⟩
   intro j r; obtain ⟨x,hJ,H,-⟩:=brig a P V X W ρ h hx hv hr hL ht (le_refl u) k j r d; exact ⟨x,hJ,H q⟩
end YM.FormalBulk08.Kemp
