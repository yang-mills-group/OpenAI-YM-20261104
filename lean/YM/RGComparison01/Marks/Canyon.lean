import YM.RGComparison01.Marks.Season
import YM.RGComparison01.Fiber
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {H : Cash W s μ L Q o C T R} {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi} {Ω : Utopia H j v d r C' χ}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
namespace Canyon
open PhysicalNext.Repeat.Deck
open Season Foreman Checks Baked Palette Pillow Selector March Opacity
variable {M:ι→Leaf R} {ρ:ι→ℝ} {z: Cl M H} {B : Ribbon R n} (V:Config G c)

lemma partOn (u:Cake M H)(h:part M ρ χ u V ≠ 0) : Ac.Spark H.supportP u.1.val ∧ troupe T R Q.halo (radiusB s) u.1.val ∧ u.2.reach⊆u.1.val:= by
   let b:= H.supportP; let P':= u.1.val
   unfold part driver likely at h
   have hx:=right_ne_zero_of_mul (right_ne_zero_of_mul h)
   by_contra! hK
   apply hx; refine sum_eq_zero fun i _ => ?_
   by_cases ht : Ac.Spark H.supportP (u.1.val) ∧ troupe T R Q.halo (radiusB s) u.1.val; swap
   · unfold Team.album; apply integral_eq_zero_of_ae
     exact Eventually.of_forall (fun z=> if_neg ht)
   exact Team.qlocalFbb_stalk _ _ (by rw [Palette.label]; exact fun hP=> hK ht.1 ht.2 hP)
lemma maskedOff {u:Cake M H}{i:ℕ} (hv : Opacity.key S i ∈ sand u)
    (hy : ∀ U,R.activities.regularOccurrence R.p i U=0) : part M ρ χ u V = 0 := by
   let x:= u.1.val; let Q':=team M u.2
   have hs : Opacity.key S i∈ x\Q'.signs S:=by unfold Q'; rw [Palette.label]; exact hv
   have hm (F:Tree.Forest S.ratio) (Y:Coat T F) k z : Polar.floating Y o.a R W Q.table z k Q.halo (x\Q'.signs S)=0 := by
       apply prod_eq_zero hs; change Real.exp (-(R.activities.regularOccurrence _ i _) * _) -1= _; rw [hy,neg_zero,zero_mul,Real.exp_zero,sub_self]
   have hq (F:Tree.Forest S.ratio)(Y:Coat T F) c : Q'.common Y x W o.a Q.table Q.halo c =0 := by
      unfold Team.common Team.floral; split_ifs
      · simp only [hm,mul_zero,integral_zero]
      simp_rw [mul_zero,integral_zero]
   have he (F:Tree.Forest S.ratio) (Y:Coat T F) : Q'.album Y x W o.a Q.table Q.halo=0:= by
       unfold Team.album; simp only [show ∀ z,Q'.aquifer (Y.rinse z) x W o.a Q.table Q.halo=0 from (fun z=>by unfold Team.aquifer; split;  simp only [likely,hq,Finset.sum_const_zero,mul_zero]; rfl),integral_zero]
   unfold part driver likely; apply mul_eq_zero_of_right; apply mul_eq_zero_of_right; apply sum_eq_zero; intro j hj; exact he _ _
-- Need Cabinet survivors before orientation moves
lemma oldVin {i : Head S} {p:Cake M H} (hx:i∈ sand p) (he : ¬ocean Ψ p) (hz : ¬scare p) (h : p.1.val.toLeft=∅)(hv:Matter.own p.1.val=∅):
    (∃ j, ¬Ψ j ∧ i=Opacity.key S j) ∨ Beam.Pennies S i:= by
   have hp := (Finset.mem_sdiff.mp hx).1; have hq : ¬ JOB S i:= fun h=>hz ⟨i,hx,h⟩
   rcases i with i|i
   · have he:= mem_toLeft.mpr hp; rw [h] at he; exact (notMem_empty _ he).elim
   rcases i with i|i|i
   · have he : i∈ Matter.own p.1.val:= mem_toLeft.mpr (mem_toRight.mpr hp); rw [hv] at he; exact (notMem_empty _ he).elim
   · rcases i with i|i|i
     · rcases i with i|i|i|i|i
       · exact Or.inl ⟨i,fun h=>he ⟨i,h,hx⟩,rfl⟩
       · exact Or.inr ⟨_,rfl,True.intro⟩
       · exact Or.inr ⟨_,rfl,True.intro⟩
       · exact Or.inr ⟨_,rfl,True.intro⟩
       exact (hq fun V t=>rfl).elim
     · exact Or.inr ⟨_,rfl,True.intro⟩
     exact (hq fun V t=>rfl).elim
   exact (hq fun V t=>rfl).elim

-- need Mint.depth
abbrev pattern (p:Cl M H) : H.fragrances:= ⟨p.1,Prod.fst ∘ p.2⟩

lemma minor (h:¬Season.Heavy k z) (he:¬ Ode Ψ z)(hh:glass M ρ χ z V≠0)(hB:Drawing.Opens B Ψ): z.1+1 ≤ k+Season.allot z ∧ coefficient (seam M H) z.2≠0 ∧ ∀ i,
    let v:= z.2 i
    Ac.Spark H.supportP v.1.val ∧ troupe T R Q.halo (radiusB s) v.1.val ∧ v.1.val.card≤ k+Season.allot z ∧
    v.2.reach ⊆ v.1.val ∧ (∀ j∈v.2.val,∃ i,(M j).turn = Wing.logKey i) ∧ ∀ p∈ sand v,p ∈ Set.range (Drawing.cabinet H B).ink := by
   have hp: ∀ i,part M ρ χ (z.2 i) V≠0:= fun i ht=> hh (by unfold glass Gas.term; rw [prod_eq_zero (mem_univ i) ht,mul_zero,zero_div]); have hx i:= partOn V (z.2 i) (hp i);
   have hV : (∑ i,(z.2 i).1.val.card) ≤ k+ Season.allot z:= by
      apply le_trans (b:=age z+Season.allot z) _ (Nat.add_le_add_right (le_of_lt (lt_of_not_ge fun ht=>h (Or.inl ht))) _)
      unfold age Season.allot; rw [← sum_add_distrib]; refine Finset.sum_le_sum fun i _=> ?_; unfold sand; rw [Finset.card_sdiff_of_subset (hx i).2.2]; have hh':= Finset.card_image_le (s:=(z.2 i).2.val) (f:=Palette.sign M S);
      have h : (z.2 i).2.reach.card ≤ (z.2 i).1.val.card:= card_le_card (hx i).2.2
      apply le_trans (b:= ((z.2 i).1.val.card-(z.2 i).2.reach.card)+ (z.2 i).2.reach.card) (by omega) (Nat.add_le_add_left hh' _)
   have hd: Height.depth H (pattern z) < radiusB s:= show drift z < radiusB s from lt_of_not_ge (fun x=>h (Or.inr (Or.inr (Or.inl x))))
   refine ⟨(le_trans (b:=Height.breadth H (pattern z)) (Beam.on_one (pattern z) (fun i=> Finset.card_pos.mpr (hx i).1.1)) hV),fun hi=> hh (by unfold glass Gas.term; rw [hi,zero_mul,zero_div]),?_⟩
   intro i v
   have ht : ¬ ocean Ψ v := fun hx=> he ⟨i,hx⟩
   obtain ⟨hS,hQ,hA⟩:= hx i
   obtain ⟨h₀,h₁⟩:= Survivors.noSeed (v.1) hQ (lt_of_le_of_lt (single_le_sum (f:=fun i=>Cash.numP (z.2 i).1.val) (fun _ _=> Nat.zero_le _) (mem_univ i)) (lt_of_not_ge (fun hx=>h (Or.inr (Or.inl hx)))))
   refine ⟨hS,hQ,(single_le_sum (f:=fun i => (z.2 i).1.val.card) (fun y _=> Nat.zero_le _) (mem_univ i)|>.trans hV),hA,fun j hj=>?_,fun p hX=>?_⟩
   · have hh:= hA (v.2.reaches_of hj); rcases h:(M j).turn with k|k; · exact ⟨_,rfl⟩
     have he : k∈ Matter.own v.1.val:= mem_toLeft.mpr (mem_toRight.mpr (by unfold Palette.sign at hh; rw [h] at hh; exact hh)); rw [h₁] at he; exact (notMem_empty _ he).elim
   have ha : ¬ scare v:= fun ht=> h (Or.inr (Or.inr (Or.inr ⟨i,ht⟩)))
   rcases oldVin hX ht ha h₀ h₁ with ⟨j,hj,rfl⟩|hp'
   · have hh : B.keep j:= by by_contra hk; exact hp i (maskedOff (M:=M) (ρ:=ρ) (χ:=χ) (u:=v) V hX (hB.anywhere j hj hk))
     exact ⟨.inr ⟨j,hh⟩,rfl⟩
   obtain ⟨p,hx⟩:= (Mint.penned ..).1 hp'
   exact ⟨.inl ⟨p,Drawing.depth_music hd p i (hx.symm ▸ ((Finset.mem_sdiff.mp hX).1 : _))⟩,hx⟩
end Canyon
end YM.RGComparison01.Pledge
