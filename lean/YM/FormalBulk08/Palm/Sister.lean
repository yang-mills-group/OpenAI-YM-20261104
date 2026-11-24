import YM.FormalBulk08.Palm.Rider

/-!
Strong result through m after summing all preimages. Use regression before
projecting low terms: algebraic no lowers, triangular block preserved with
eng price right orientation.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Palm
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge} {m d l e n j t D :ℕ}{A B η σ:ℝ}{L: Side}{o:Loc G 1}
lemma emerge (o:Loc G 1) (F:Frame G d)(S:Cross L (Loc G 1) (Loc G 1))(Y: Anthem D G)(hS:S.strip η A)(hs:0<η)(hA:0≤A)(hL:2≤L.val)(p: Studio D)(i:F.Index)(e n :ℕ)(he:η≤ L.val*σ)(h:∀ p,∃ Z,Knoxville (fame _) σ (0,o) (Y p e n) Z):
   (∃ Z, Knoxville (fame _) η (0,o) (towerV S Y d e n hL p) Z) ∧ pearlJ F (towerV S Y d e n hL p) i=aven L d*∑ x:Site L, pearlJ F (upmost L x S (Y (throughW x D hL p) e n)) i:= by
    choose Z H using h; have Hx x:=upheave (o:=o) _ x hS hA he hs.le (H (throughW x D hL p)); have he':= knox_sum Finset.univ (fun x _=> Hx x); unfold towerV
    refine ⟨⟨_,he'.smul _⟩,?_⟩; rw [chalk_amp F _ he' hs];exact congr_arg (aven L d*·) ((chalked F Finset.univ (fun i _=>⟨η,_,hs,Hx i⟩) i).2)
lemma council (o:Loc G 1)(F:Frame G d)(Y: Anthem D G)(hq:Clef o Y l)(q:ℕ)(hp:d<D)(he:q≤d)(i:Letter F)(hz:slots F i=n)(hx:Pose.weight F i≤q)(P:Flight j t)(hd:d≤j)(ht:4≤t)(H:Hol G)(K:KernelChoices)(hs:0<σ)(hB:Bonds F o σ q e n Y 0)(hL:2≤P.L.val)(hA:∀ p:Studio D,∃ Z, Knoxville (fame _) σ (0,o) (Y p e n) Z)(hη:0<η)(hw:η≤P.L.val * σ)(hX:(linesOf P K.penalty).strip η A)(hu:0≤A) :
   pearlJ F (towerV (chair P G K) Y d e n hL (inside F i D)) (mint F i)=heightK P.L d (Pose.weight F i)* pearlJ F (Y (inside F i D) e n) (mint F i):= by
   rw [(emerge o F (chair P G K) Y (grown_budget G _ hu hX) hη hu _ _ _ _ _ hw hA).2]; simp_rw [traction o F Y hq q hp he i hz hx P hd ht H K hs hB _ _ hA hη hw hX hu]; rw [← abs_of_pos (aven_pos P.L d), income_by, ←mul_assoc]; rfl
lemma inclusive (o:Loc G 1)(F:Frame G d)(l n q e D:ℕ)(hp:d<D)(hq:q≤d+1)(i:Letter F)(hz: slots F i=n)(hx:Pose.weight F i< q)(U:Side)(j t:ℕ)(hd:d≤j)(hj:4≤j)(ht:4≤t)(H:Hol G)(K:KernelChoices)(hs:0<σ):
    ∃ C:ℝ,0≤C∧∀ P:Flight j t,P.L=U→∀ hL:2≤P.L.val,∀ Y:Anthem D G,Clef o Y l→∀ B:ℝ,Bonds F o σ q e n Y B →(∀ p:Studio D,∃ Z, Knoxville (fame _) σ (0,o) (Y p e n) Z)→∀ η A:ℝ,0<η → η ≤ P.L.val * σ → (linesOf P K.penalty).strip η A → 0≤A →
     ‖pearlJ F (towerV (chair P G K) Y d e n hL (inside F i D)) (mint F i)‖≤ C*B:= by
     obtain ⟨C,hC,H⟩:= counting o F l n q e D hp hq i hz hx U j t hd hj ht H K hs; refine ⟨(U.val:ℝ)^d*C,by positivity,fun P he hL Y hY B hB hz η A hη hw hX hA=>?_⟩; rw [(emerge o F (chair P G K) Y (grown_budget G _ hA hX) hη hA _ _ _ _ _ hw hz).2,_root_.norm_mul]; refine (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum (fun x _=> H P he x hL Y hY _ hB hz _ _ hη hw hX hA))) (norm_nonneg _)).trans_eq ?_
     rw [Real.norm_eq_abs, income_by, he, ←mul_assoc]
lemma lease_cut (o:Loc G 1)(U:Tile (edgeL G) m)(h:Knoxville (fame _) σ (0,o) U 0) : U=0:= by
    funext v; exact norm_le_zero_iff.mp (le_of_not_gt fun hP=>(not_lt_of_ge (penn_chill v h)) (mul_pos hP (Real.exp_pos _)))
end YM.FormalBulk08.Palm
