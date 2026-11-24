import YM.MS.Tone.Blip
/-!
# Color and reality timbre

S test external legs on cover lattice unintegrated or translated. ∆ high still multiplexed;
    keep orientation on Net if restricted. Proof for color reciprocity enough all.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Tone
open Function Filter Set Finset Plane Koszul Cylinder Lab Lattice Native Bare Focus Landau Momentum Paint Color
open scoped Topology ContDiff
variable {G:Gauge}
local notation "W" => Dot G Cover
local notation "E" => LightMode G Cover
local notation "B" => Branch G Axis
local notation "V" => LightMode G QP

-- supports color at finite despite frequencies. Ink & basis Act.
lemma dye_pass (F:W){s:Finset Cover}(h:BoundBy (s:Set Cover) F)(u:G.El): BoundBy (s:Set Cover) (dye u F):= by
    refine Cylinder.Slim.stretch F h (fun i hi j he=>?_)
    suffices j.2=i.2 from (show j.2∈s from this ▸ (show i.2∈s from hi))
    exact Classical.byContradiction fun H=> he (offC _ _ _ _ (fun h=> H (congr_arg (fun u:Atom Axis × Cover=> u.2) h)))
lemma caps (F:W)(u:G.El) : repeatC u (run F)=run (dye u F):= by
    funext l; induction l generalizing F with
    | nil=> simp [dye,paint,run]
    | cons a l ih=>
       obtain ⟨s,hs⟩:=obliges F; rcases a with ⟨⟨a,b⟩,p⟩; rw [repeat_cons,grows _ (dye_pass F hs u)]
       have he i: setLeg (((a,b),p):V) i=((a,i),p):=rfl
       simp_rw [he,tips F hs,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,ih,solok,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply, Finset.mul_sum]
       rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; dsimp [bornv]; ring
lemma mirror_bill (F:W)(h:Still F.val) (w:List V): star (run F w)=run F (invertMom w):= by
    induction w generalizing F with
    | nil=> exact h []
    | cons i l ih=>
        obtain ⟨s,hs⟩:=obliges F; rw [grows F hs,star_sum]; unfold invertMom; simp_rw [List.map_cons,grows F hs]; exact Finset.sum_congr rfl (fun x _=> by rw [star_mul',starbill,ih (enter _ F) (h.D _)]; rfl)
lemma blockSolid (q:ℤ)(F:W)(h:Tuned F q)(he:Colorless F)(b:Bool): Solid b (run F) q where
    symm _ _ _ _ _:= tied.sym F h.symm ..
    color w _ i:= by rw [← rep_book,caps,he]
    real' w _:= (mirror_bill F h.still w).symm
    ghost w _ hx:= h.ghost.shades (T:=paywave) F (fun i j hi=> congr_arg ghostNo (in_light _ _ hi)) w hx -- inference

section rotate
open Orient
variable (k:Signed)
lemma moved (i:E): bornv (turn k i)=k.act (bornv i):= by
    unfold bornv; rcases i with ⟨⟨⟨_|i,b⟩,t⟩,x⟩ <;> simp only [turn,Signed.act_add,here_b,here_a,Signed.act_zero, emb_H]
    have hm (c:ℝ)(p:QP): k.act (c • p)= c • k.act p:= by funext i; unfold Signed.act; split <;> simp [*]
    rw [purse_base]; cases hv:k.flip i
    · simp only [Bool.false_eq_true,if_false,hm,emb_H,stepflip k i,hv,if_false];
    simp only [if_true,hm,emb_H,stepflip k i,hv,if_true,emb_neg,idRail,Native.Chart.endRail,Signed.act_add]; rw [emb_add,emb_neg]; ext; simp; split_ifs <;> ring
-- inversion ext action intrinsic sign from Lab. 
lemma repose (w:Legs V): net (w.map (permute k))= k.act (net w):= by induction w with| nil=> simp [net]| cons a l ih=> simp only [net_cons,List.map_cons,ih]; exact (Signed.act_add k ..).symm
lemma shiftleg (p:V)(x:E): paywave (permute k p) (turn k x)=paywave p x:= by
    unfold paywave; rw [moved];
    have ht : (permute k p).1=(turn k x).1 ↔ p.1=x.1:= by rcases p with ⟨⟨⟨_|_,b⟩,i⟩,p⟩ <;> rcases x with ⟨⟨⟨_|_,d⟩,j⟩,x⟩ <;> simp [permute,turn]
    have hh : way id (permute k p).1 (turn k x).1 (R:=ℂ)= way id p.1 x.1:= by
       by_cases hu:p.1=x.1
       · exact (if_pos (ht.mpr hu)).trans (if_pos hu).symm -- Decidable defeq?
       exact (need id (show (permute k p).1≠id (turn k x).1 from fun h=> hu (ht.mp h))).trans (need id hu).symm
    rw [hh]; exact congr_arg _ (turnC ..)
lemma σ_eq (p:V)(x:E): p.1=x.1 → σ k x=negateField k p:= by
    intro h; simp only [σ,negateField,h,fee]; split
    · rename_i x hx; norm_num [hx]
    rename_i i hx; cases hk:k.flip i <;> simp [hx,hk]
lemma by_shift (F:W)(w:List V): run (pose k F) (w.map (permute k))=(w.map (negateField k)).prod * run F w := by
   unfold run pose; rw [LinearMap.comp_apply,study,view_cost];
   -- from shade argument, substitution on x metadata
   let T (p:V)(x:E):=paywave p (turn k x)*σ k x
   induction w generalizing F with
   | nil=> simp
   | cons a l ih=>
       obtain ⟨s,hs⟩:=fromCyl F; simp only [List.map_cons,deriv_lum (fun i j=>paywave i (turn k j)*σ k j) (permute k a) _ hs,deriv_lum paywave a F hs,List.prod_cons,Finset.mul_sum]; -- `T` not let unfolded
       apply Finset.sum_congr rfl; intro i _; rw [shiftleg]; by_cases he:paywave a i=0; simp [he]; rw [σ_eq k a _ (in_light a i he), ih]; ring
end rotate
end YM.MS.Tone
