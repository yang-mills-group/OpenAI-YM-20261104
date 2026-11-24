import YM.OPE.Therm.Kiln
import YM.Cells.Proximity
/-!
# Site-to-site box seams

We work with overlapping site tiles; the *links* later left on seams are
those never touching a chamber. Occasions for equality use integer coordinates.
Do not project a flag on a seam to one cell except where its entire face fits.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm.House
open Function Filter RG Lattice Wilson MeasureTheory Cells
open scoped BigOperators Classical Topology
variable {n:Side}
variable (T:Tiling n) {v u:T.Cell} {x y:Site n} {a i:Axis} {r:ℕ}
local notation "γ"=> T.coordinated
local notation "N"=>T.side.val
local notation "φ"=>T.residue
local notation "∆"=> T.chamber

/-- With site `.kind` this includes BOTH seams. Corners and creases support chamber-local plaquettes. -/
def hall (v:T.Cell)(x:Site n): Prop := ∀ i:Axis, γ v x i ≤ N
def suite (v:T.Cell) : Support n:= Finset.univ.filter (hall T v)
lemma host : x∈ suite T v ↔ hall T v x:= by simp [suite]
section
-- axis index formulas
lemma floorGen (h : γ v x a < N) : T.which x a=v a ∧ φ x a=γ v x a := by
   let g : Tiling n:= { T with kind:=.link}
   let y := update (T.starts v) a (x a)
   have hy:y a=x a:= update_self ..
   have he : y∈g.chamber v:= by
      intro i; by_cases hi:i=a
      · subst i; change (y a-T.starts v a).val<_; rw [hy]; exact h -- subst i or a?
      change (y i-T.starts v i).val < N; unfold y; simp only [update_of_ne hi,sub_self,ZMod.val_zero]; exact T.side.pos
   have hc := g.which_chamber he; have hv := (congr_fun hc a).symm; have ht := g.residual y a; rw [hc] at ht
   have hx : T.coordinated v y a= γ v x a:= by unfold Tiling.coordinated; rw [hy]
   constructor
   · change g.which x a=_; rw [hv]; -- rewrites lhs? hv v=g
     unfold Tiling.which Tiling.whole Tiling.grid; rw [hy]
   have hp : φ y a= φ x a:= by unfold Tiling.residue Tiling.grid; rw [hy]
   exact hp ▸ (((show φ y a= γ v y a from ht.symm).trans hx))
lemma ach (x:Site n) (a:Axis): γ (T.which x) x a < N := by
   rw [T.residual]; exact Nat.mod_lt _ T.side.pos
lemma hiCoord (h: γ v x a=N) : γ (v+step a) x a=0 ∧ T.which x a=v a+1∧φ x a=0:=by
   have ht: T.starts (v+step a) a=T.starts v a+N:=by unfold Tiling.starts; rw [map_add,T.root_step]; simp [add_assoc]
   have hf: T.starts (v+step a) a=x a:= by rw [ht,← h,T.indent]
   have he: γ (v+step a) x a=0:=by unfold Tiling.coordinated;simp [hf];
   obtain ⟨hp,hP⟩:=floorGen T (he.trans_lt T.side.pos); refine ⟨he,?_,hP.trans he⟩; simpa using hp
lemma hall_which (x:Site n): hall T (T.which x) x:=fun i=> (ach T x i).le
lemma enters (h:x∈∆ v) : hall T v x:= fun i=> (T.small h _).le
end
section strict
variable (hv:T.kind=.site)
include hv
lemma interior : x∈∆ v ↔ ∀ i,0<γ v x i ∧ γ v x i<N:= by
   apply forall_congr'; intro i; -- rewrite Strict without dep
   change Kind.Strict T.kind N (γ v x i) ↔ _; rw [hv]; rfl
lemma entrance (h:x∈∆ v) (h':hall T u x) : v=u:= by
   have hx := T.which_chamber h; funext i; specialize h' i; obtain ⟨hp,hP⟩:= interior T hv |>.mp h i
   rcases eq_or_lt_of_le h' with he|ht
   · have ha := ((hiCoord T he).2.2); exfalso; rw [show φ x i=γ v x i from (floorGen T hP).2] at ha; omega
   exact (congr_fun hx i).symm.trans (floorGen T ht).1
lemma spinsCoord (v:T.Cell)(x:Site n)(a:Axis) : (γ v (T.copyMap v x) a : Per n)=
      if ((T.omega v).flip a) then (N:Per n) - γ 0 x a else γ 0 x a := by
   simpa [Tiling.coordinated,hv, Per,Kind.shift] using (T.copy_formula v x a)
lemma cipher (v:T.Cell)(x:Site n)(a:Axis)(h:γ 0 x a≤N): γ v (T.copyMap v x) a=
      if ((T.omega v).flip a) then N- γ 0 x a else γ 0 x a:= by
   have hq : γ v (T.copyMap v x) a<n.val:= ZMod.val_lt _; have hc:= spinsCoord T hv v x a
   cases he:(T.omega v).flip a <;> rw [he] at hc
   · simpa only [Bool.false_eq_true,↓reduceIte] using! (show γ v (T.copyMap v x) a= γ 0 x a from by
        simp only [Bool.false_eq_true,↓reduceIte] at hc
        simpa only [ZMod.val_natCast_of_lt hq,ZMod.val_natCast_of_lt (h.trans_lt T.narrow)] using congr_arg ZMod.val hc)
   simp only [↓reduceIte] at hc ⊢; rw [← Nat.cast_sub h] at hc; simpa only [ZMod.val_natCast_of_lt hq,ZMod.val_natCast_of_lt ((Nat.sub_le _ _).trans_lt T.narrow)] using congr_arg ZMod.val hc
lemma turnsHall (v:T.Cell)(x:Site n) : hall T v (T.copyMap v x) ↔ hall T 0 x:= by
   constructor
   · intro h a; let y:= T.copyMap v x; let z:= γ v y a; let u:= γ 0 x a
     have hp:= spinsCoord T hv v x a; have hh : z ≤ N:= h a; have he : u<n.val:=ZMod.val_lt _
     change (z:Per n)=if _ then _-u else u at hp
     split at hp
     · rw [eq_sub_iff_add_eq] at hp; have hb : (u:Per n)=(N:Per n)-z:= eq_sub_of_add_eq (by rw [add_comm]; exact hp); rw [← Nat.cast_sub hh] at hb; have hy: u=N-z:=by simpa only [ZMod.val_natCast_of_lt he,ZMod.val_natCast_of_lt ((Nat.sub_le _ _).trans_lt T.narrow)] using congr_arg ZMod.val hb
       exact hy.trans_le (Nat.sub_le _ _)
     have ha:z=u:=by simpa only [ZMod.val_natCast_of_lt he,ZMod.val_natCast_of_lt (hh.trans_lt T.narrow)] using congr_arg ZMod.val hp
     exact ha.symm.trans_le hh
   intro h a; rw [cipher T hv v x a (h a)]; split; exact Nat.sub_le _ _ ; exact h a
lemma turnsSuite (v:T.Cell): suite T v= (suite T 0).image (T.copyMap v):=by
   ext x; obtain ⟨x,rfl⟩:= T.pointed v x;  have h : Injective (T.copyMap v):=(Push.Local.turnSites (T.omega v) (T.translateBy v)).injective
   simp [Finset.mem_image,h.eq_iff,host,turnsHall T hv]
end strict
section gross
-- interior-visibility is only used at the original site tiling, not translated continuation
lemma slide (v:T.Cell){x:Site n} (a:Axis) (h:γ v x a<N) : γ v (x+step a) a=γ v x a+1:=by
   let i:= γ v x a; have hp:((i+1:ℕ) : Per n)=(x+step a:Site n) a - T.starts v a:=by simp [i,Tiling.coordinated,Per]; abel
   unfold Tiling.coordinated; rw [← hp,ZMod.val_natCast_of_lt ((show i+1 ≤N from h).trans_lt T.narrow)]; rfl
lemma sleeps (x:Site n) (a:Axis) : hall T (T.which x) (x+step a):=by
   intro i; by_cases hi:i=a
   · subst i; rw [slide T _ _ (ach ..)]; exact ach ..
   unfold Tiling.coordinated; simpa only [Tiling.coordinated,Pi.add_apply, step_apply, if_neg hi, add_zero] using (hall_which T x i)
lemma suite_front (x:Face (Per n)): touched x ⊆ suite T (T.which x.1):=by
   obtain ⟨x,i⟩ := x; let v:= T.which x; let a:= i.val.1; let b:=i.val.2; have h:a≠ b:= i.property.ne
   intro y hy; rw [touched,square_corners] at hy; change y ∈ ( [x,x+step a,x+step a+step b,x+step b,x]: List (Site n)).toFinset at hy
   simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hy
   apply host T |>.mpr; rcases hy with rfl|rfl|rfl|rfl|rfl
   · exact hall_which T y
   · exact sleeps T x a
   · intro j; by_cases hh:j=b
     · subst j; have he : γ v (x+step a) b = γ v x b:= by unfold Tiling.coordinated; simp [Ne.symm h];
       exact (slide T v b (he.trans_lt (ach T x b))).trans_le (he.trans_lt (ach T x b))
     have he : γ v (x+step a+step b) j= γ v (x+step a) j:= by unfold Tiling.coordinated; simp [hh]
     exact he.trans_le (sleeps T x a j)
   · exact sleeps T x b
   exact hall_which T y

-- wide room margin cards explicit later
lemma deed (v:T.Cell)(r:ℕ){x:Site n}(h:x ∈ T.margin v (r+1)): (halo r {x}: Set (Site n)) ⊆ T.chamber v:= by
   intro y hy; obtain ⟨i,hi,hI⟩:= halo_spec.mp hy;rw [Finset.mem_singleton] at hi; subst i; rw [separation_comm] at hI
   suffices hh:wrap n (lift (y-x))+x∈ T.chamber v from (by simpa using hh)
   exact T.fits_stencil h fun a=> Nat.lt_add_one_iff.mpr ((component_le _ a).trans hI)
end gross
end YM.OPE.Therm.House
