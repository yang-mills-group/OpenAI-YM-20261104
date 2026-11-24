import YM.X.Chir.Sparkle
/-!
# Any height ≥3 single Green differential wire travels with exterior costs, seen as horizontal curl⊗ potential. ∆ budget.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Gravity
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R:ℝ}
variable (a:G.ColorIndex)
local notation "H"=> Reed.Horizontal G
lemma lateral (i j:Axis)(h:i≠j): arc a 0 i j∈ Reed.Horizontal G:= by
    rcases lt_or_gt_of_ne h with h|h; · exact Submodule.subset_span ⟨(0,⟨(i,j),h⟩,a),rfl⟩
    rw [show arc a 0 i j= -(arc a 0 j i) from (by rw [arc_diff,arc_diff]; abel)]; exact (Reed.Horizontal G).neg_mem (Submodule.subset_span ⟨(0,⟨(j,i),h⟩,a),rfl⟩)
lemma lift_off (l:List Axis)(i:Axis)(v:Cover): ∃ (f:Marks G)(j:Axis), f.k=(i::l).length ∧ pathS f.x (columnA j a).x= graphS (i::l) v:= by
   induction l generalizing i with
   | nil=>
       obtain ⟨j,hj⟩:= exists_ne i; let f:= Stems.arc a 0 i j; have hp:f∈ H:= lateral a i j hj.symm; have hf:f∈ Reed.grads G 1:= by unfold f; rw [arc_diff]; exact Submodule.sub_mem _ (grad_row _ _) (grad_row _ _)
       refine ⟨⟨1,leadsL v f, grad_lead v _ hf, horizontal_lead v _ hp⟩, j,rfl,cast_inj ?_⟩; rw [cast_path,cast_graph]; ext n x y; change spend n x y (leadsL v f) _= _; rw [spend_subx]; unfold f; rw [arc_diff,map_sub,LinearMap.sub_apply,column_d,column_d]; simp [ls,Ne.symm hj,hj, graphS,graphK,map_add,map_sub,show ∀ x v y:Site n,x+v-y=x-y+v from fun _ _ _=>by abel]
   | cons j l IH=>
       obtain ⟨f,x,hp,hf⟩:= IH j; refine ⟨⟨f.k+1,leadsL (step i) f.x-f.x,fan_triangle _ f.order i, (Reed.Horizontal G).sub_mem (horizontal_lead _ _ f.sector) f.sector⟩, x, ?_, cast_inj ?_⟩; · change f.k+1=(i::j::l).length; rw [hp,show (i::j::l).length=(j::l).length+1 from by simp]
       apply_fun castG at hf; rw [cast_path,cast_graph] at hf; rw [cast_path,cast_graph]; ext n y z; change spend n y z (_-_) _=_; rw [map_sub,LinearMap.sub_apply,spend_subx, show ∀ x:Cover,spend n x z f.x (columnA _ a).x= _ from fun x=> congr_fun (congr_fun (congr_fun hf n) x) z]; rw [show spend n y z f.x (columnA _ a).x= _ from congr_fun (congr_fun (congr_fun hf n) y) z,slopeX] -- syntax fix
-- generic air span equals
lemma air_span : air k=Submodule.span ℝ {A| ∃(l:List Axis)(z:Cover), l.length=k ∧ A=graphS l z}:= by
   let K := {A: Scaff| ∃(l:List Axis)(z:Cover),l.length=k ∧ A=graphS l z}; have he: bird k≤ (Submodule.span ℝ K).map castG:= by
      apply Submodule.span_le.mpr; rintro _ ⟨l,h,v,rfl⟩; exact ⟨_,Submodule.subset_span ⟨l,v,h,rfl⟩,cast_graph l v⟩
   apply le_antisymm; · intro p hp; obtain ⟨a,ha,hf⟩:= he (sky.mp hp); exact cast_inj hf ▸ ha
   apply Submodule.span_le.mpr; rintro _ ⟨l,v,h,rfl⟩; exact air_graph _ _ h
lemma air_ds (i:Axis){f:Scaff}(h:f∈air k): ds i f∈air (k+1):= by
    rw [air_span] at h; induction h using Submodule.span_induction with| mem i hv=> obtain ⟨l,x,h,rfl⟩:=hv; rw [graph_d]; exact Submodule.neg_mem _ (air_graph _ _ (by rw [List.length_cons,h]))| zero=>rw [map_zero];exact Submodule.zero_mem _| add a b _ _ h g=>rw [map_add];exact Submodule.add_mem _ h g| smul a b _ h=>rw [map_smul]; exact Submodule.smul_mem _ _ h
local notation "ε"=> epsilon q
variable (χ:Floor R)(hq:1<q.val)(x y z: Fielding.Walk)(h: Geom q r x y z)(hr:R<r)
lemma sprite_val (e:ℝ)(f:Scaff)(i:ℕ)(n:Side)(x y:Site n): sprite e i f n x y=(e^(2+i))⁻¹ * f n x y:=rfl
def skyView (q:ℕ+)(x:Fielding.Walk)(k:ℕ): Scaff→ₗ[ℝ] Weave q where
   toFun A i:= fun z=> ↑(sprite (epsilon q i) k A (side q i) (wrap _ (x i)) z)
   map_add' a b:= by ext1 i; ext1 z; simp [sprite,mul_add]
   map_smul' a b:= by ext1 i; ext1 z; change Complex.ofReal ((epsilon q i ^(2+k))⁻¹* (a * _))= a • (↑(_:ℝ):ℂ); simp [mul_left_comm,sprite]
include χ h hq hr a
lemma lift_view (l:Scaff)(i:ℕ)(hl:l∈ air i)(hi:0 < i)(A B:Marks G)(a' b':Tops G): Released (crow q (skyView q x i l* wire q y A a' * wire q z B b')):= by
    -- choose color a; other marks may exist for neutral groups, require a
    rw [air_span] at hl; induction hl using Submodule.span_induction with
    | mem l hl=>
        obtain ⟨l,v,hl,rfl⟩:=hl; cases l with
        | nil=>rw [List.length_nil] at hl;omega
        | cons u l=>
          obtain ⟨f,j,he,hf⟩:= lift_off a l u v; rw [show skyView q x i (graphS (u::l) v)= wire q x f (columnA j a) from ?_]; have hh:=distinct_cost q x y z χ h hq hr [(f,columnA j a)] [(A,a')] [(B,b')] rfl rfl rfl; simpa only [arrows_next,arrows0,mul_one,one_mul] using hh
          ext1 k; ext1 y; unfold wire; rw [feeK _ _ _ _ (epsilon_pos ..),wrap_lift]; unfold cutF upMark; rw [hf, he,hl]; rfl -- check
    | zero=> rw [map_zero,zero_mul,zero_mul]; rw [show crow q 0=0 from funext (fun k=> by simp [crow])]; exact Released.zero
    | add l k _ _ hx hy=> rw [map_add,add_mul,add_mul,crowd_plus]; exact hx.add hy
    | smul a l _ hx=> rw [map_smul,smul_mul_assoc,smul_mul_assoc, RCLike.real_smul_eq_coe_smul (K:=ℂ), crowd_scale]; exact crew.smul_mem _ hx
end YM.PositionX.Chir
