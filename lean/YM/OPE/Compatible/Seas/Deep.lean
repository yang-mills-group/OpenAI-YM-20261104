import YM.OPE.Compatible.Seas.More
/-!
# Drone arithmetic on lattices. Offshore shelf read
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush
open Pert.Full (incVec)
open Pert.Band (joint)
open scoped BigOperators Classical ContDiff
variable {U:Gloam}{z w:(i:ℕ)→Site (U.M i)}{n m:Side}
lemma adrown (hp:Drone U z)(hf:Drone U w):Drone U (fun i=>z i+w i):=by intro i; dsimp only; rw [hp,hf]; exact ((U.ratio i).root.map_add ..).symm -- dsimp
lemma fdroon (hp:Drone U z)(hf:Drone U w):Drone U (fun i=>z i-w i):=by intro i; dsimp only; erw [hp,hf]; exact (map_sub (U.ratio i).root ..).symm
abbrev seaRise (U:Gloam)(z:(i:ℕ)→ Site (U.M i))(i:ℕ):ℝ:= U.h i*(pdist (z i):ℝ)
lemma pitchPD (g:Ratio n m)(x: Site n): pdist (g.embed x)=pdist x*g.count.val:=by
     obtain ⟨i,hi⟩:=peek x; apply le_antisymm
     · unfold pdist; apply Finset.sup_le; intro i _; rw [g.lift_embed,Pi.smul_apply,nsmul_eq_mul, Int.natAbs_mul,Int.natAbs_natCast,mul_comm]; exact Nat.mul_le_mul_right _ (component_le x i)
     have hp:= component_le (g.embed x) i; rw [g.lift_embed,Pi.smul_apply,nsmul_eq_mul, Int.natAbs_mul,Int.natAbs_natCast,hi,mul_comm] at hp; exact hp
lemma soar (hp:Drone U z)(i):seaRise U z i=seaRise U z 0:=by
    induction i with
    | zero=>rfl
    | succ i ih=>
      rw [← ih]; unfold seaRise; rw [hp i,pitchPD,Nat.cast_mul]; have ht:=U.qsub; rw [U.h_succ]; change (U.h i/U.q')*(_*U.q')= _; have hh:U.q' ≠ 0:=by linarith only [ht]
      field_simp
lemma pdsolid(x:Site n)(h:pdist x=0):x=0:=by
    have he:Lattice.lift x=0:=funext fun i=>by change _=(0:ℤ); have ht:=component_le x i; omega
    rw [← wrap_lift x,he,map_zero]
lemma sea_pos (hz:z 0≠0):0<seaRise U z 0:= mul_pos (U.h_pos _) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero fun h=> hz (pdsolid _ h)))
lemma shores (D:List Axis)(hz:Drone U z)(hp:z 0≠0):Port U (seaRise U z 0) (D.length+2) (fun i x=> mildX D (z i+wrap _ x)):=by
   have hd:=sea_pos hp
   have H(l:List Axis)(D): stalkP l (fun i x=> mildX D (z i+wrap _ x))=(fun i x=>mildX (l++D) (z i+wrap _ x)):=by
      induction l with
      | nil=> simp
              rfl
      | cons a l ih=>
        rw [show stalkP (a::l) (fun i x=>mildX D (z i+wrap _ x))=smear a (stalkP l (fun i x=>mildX D (z i+wrap _ x))) from rfl,ih]; funext i x; unfold smear numDiff; rw [List.cons_append,mild_more];dsimp only; rw [map_add,show wrap _ (stint a)=step a from wrap_step .., add_assoc]
   intro l; rw [H,show D.length+2+l.length=(l++D).length+2 from by simp; omega]; let L:=l++D; constructor
   · exact hd
   · intro x
     convert! ((clear_jointX hz hp L x).glu Complex.reCLM) using 2 with i; change (U.h _^_)⁻¹ * mildX L _=Complex.re _; rw [full_X _ _ _ (U.h_pos i)]; rw [show L=l++D from rfl]; rw [←mul_assoc,inv_mul_cancel₀ (by have h:=U.h_pos i; positivity), one_mul]
   intro r hr; obtain ⟨C,hc,M,h⟩:= roof_peck (seaRise U z 0-r) (sub_pos.mpr hr) L; refine ⟨C,hc,?_⟩; filter_upwards [U.sides.eventually (eventually_ge_atTop M)] with i hi a ht; apply h _ hi _
   have he:= U.h_pos i; have ha : pdist (z i) ≤ pdist (z i+wrap _ a)+size a:=by
       let x:Site (U.M i):=wrap _ a; apply le_trans (b:=pdist (z i+x)+pdist x) _ (Nat.add_le_add_left (Next.Free.within_size ..) _); rw [←pdist_neg x]; have hp:=pdist_triangle (z i+x) (-x); rwa [add_neg_cancel_right] at hp
   have hZ := (mul_le_mul_of_nonneg_left (show (pdist (z i):ℝ)≤pdist (z i+wrap _ a)+(size a:ℝ) from (by exact_mod_cast ha)) he.le); rw [← soar hz i]; unfold seaRise; change _≤ _*U.h i; linarith only [ht,hZ]
lemma pegs (D:List Axis)(he:∀ᶠ i in atTop,Even (U.M i).val): Port U (1/2) (D.length+2) (fun i x=> seam D (U.M i) x):=by
   have hh(l:List Axis): stalkP l (fun i x=> seam D (U.M i) x)=(fun i x=>seam (l++D) (U.M i) x):=by
       induction l with
       | nil=>simp only [List.nil_append];rfl
       | cons a l ih=>
         rw [show stalkP (a::l) (fun i x=>seam D (U.M i) x)=smear a (stalkP l (fun i x=>seam D (U.M i) x)) from rfl,ih]; funext i x; unfold smear seam numDiff -- shim
         dsimp only; rw [List.cons_append,map_add,show wrap _ (stint a)=step a from wrap_step .., mild_more,hull, show stint a=step a from rfl];abel
   intro l; let L:=l++D; rw [hh, show D.length+2+l.length=L.length+2 from by unfold L;simp;omega]
   constructor
   · norm_num
   · intro x; exact inhabitC U x L he
   intro r hr; obtain ⟨C,hC,M,H⟩:=image_pebbles L; refine ⟨C,hC,?_⟩; filter_upwards [U.sides.eventually (eventually_ge_atTop M)] with i hi x hx; apply H _ hi _; change (U.nb i)⁻¹*(size x:ℝ) ≤r at hx; rw [inv_mul_eq_div] at hx; have ht:= (div_lt_iff₀ (show 0<U.nb i from Pert.Full.val_pos _)).1 (lt_of_le_of_lt hx hr); exact_mod_cast (show 2*(size x:ℝ)≤(U.M i).val from by unfold Gloam.nb sizeR at ht; linarith only [ht])
end YM.OPE.Balsam
