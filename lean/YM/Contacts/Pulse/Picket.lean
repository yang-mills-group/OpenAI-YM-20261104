import YM.Contacts.Pulse.Edd
import YM.Push.FREE_RESOLVENT.GaugeProjection
/-! # Block-synchronous tree slices. select is deterministic on the entire
cover from the residue and axis priority, see Tree.select. Don't quotient by
harmonic alias. Need also equivariance wrt inversion when using Orbifold. -/
noncomputable section
namespace YM.Pulse.Spine
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Tree
open Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Extension.UV.Linear
open scoped Classical Topology BigOperators NNReal ENNReal Matrix
variable {G:Gauge}{L c f n:Side}{T:Ratio c f}
namespace Larch
def tags (x:Cover): Finset Axis:= univ.filter (fun i=> x i ≠ 0)
def height (x:Cover): Axis:= if h:(tags x).Nonempty then (tags x).min' h else 0
lemma tall (x:Cover)(h:x≠0): x (height x)≠0:= by
  have he : (tags x).Nonempty:= by obtain ⟨i,hi⟩:= Function.ne_iff.mp h; exact ⟨i,by simpa [tags] using hi⟩
  rw [height,dif_pos he]; exact (mem_filter.mp (min'_mem _ he)).2
lemma mirror (x:Cover): height (-x)=height x:= by
  have hh: tags (-x)=tags x:= by ext; simp [tags]
  rw [height,height]; congr!
lemma plank (L:Side)(hi:Odd L.val)(x:Site L): lift (-x)=-lift x:= by
  obtain ⟨k,hk⟩:=hi; refine lift_eq_iff.mpr ⟨?_,fun i=>?_⟩; simp; have hv := lift_centers x i; rw [Pi.neg_apply]; omega

def steer (x:Cover): Step:= if x (height x)<0 then posDir (height x) else negDir (height x)
lemma stake (x:Cover)(h:x≠0): steer (-x)=⟨(steer x).dir,!(steer x).neg⟩:= by
  have he:= tall x h; unfold steer; simp_rw [Pi.neg_apply,mirror]; by_cases H:x (height x)<0 <;> split_ifs <;> first | rfl | omega
lemma rises (x:Cover)(h:x≠0) : size (x+(steer x).vec) < size x := by
  let a:=height x; let d:= steer x; have ha:= tall x h
  have he : ((x+d.vec:Cover) a).natAbs < (x a).natAbs:=by unfold a d steer; split <;> simp <;> omega
  apply sum_lt_sum (f:=fun i=> ((x+d.vec:Cover) i).natAbs) (g:=fun i=>(x i).natAbs) ?_ ⟨a,mem_univ _,he⟩; intro i _; by_cases hi:i=a
  · exact hi.symm ▸ he.le
  unfold d steer; change i ≠ height x at hi; split <;> simp [hi]
lemma unable (x:Cover)(h:x≠0)(R:ℕ)(H:x∈box R): x+(steer x).vec ∈ box R := by
  rw [box_iff_layers] at *; intro i; have he:= tall x h; have hp:=H i; unfold Lattice.layers at *; unfold steer; rw [Finset.mem_Icc] at hp ⊢; by_cases hi:i=height x <;> split_ifs <;> simp [hi] at hp ⊢ <;> omega
lemma fallen (x:Site f) : leaf T x ↔ T.residue x≠0:= not_congr (T.root_id x)
def planting (T:Ratio c f)(ho:Odd T.count.val) : Forest T where
  up x:= steer (lift (T.residue x))
  height x:= size (lift (T.residue x))
  bound x:= by
    let r:= T.residue x; change size (lift r) ≤ _; apply le_trans (b:= ∑ i:Axis,T.count.val) (sum_le_sum ?_) (by simp [Axis])
    intro i _; have h:= (box_iff_layers ..).mp (T.half_box ho r) i; simp [Lattice.layers] at h; omega
  rise x hx:=by
    have h : lift (T.residue x)≠0:= fun e=>(fallen _).mp hx (by rw [← wrap_lift (T.residue x),e,map_zero]); exact ((congr_arg size (T.internal ho (unable _ h _ (T.half_box ho _))).1).trans_lt (rises _ h))
  stays x hx:= (T.internal ho (unable _ (fun e=>(fallen _).mp hx (by rw [← wrap_lift (T.residue x),e,map_zero])) _ (T.half_box ho _))).2

def seed (z:Site L)(i:Axis): Prop:= (z≠0 ∧ steer (lift z) = ⟨i,false⟩) ∨ (z+step i≠0 ∧ steer (lift (z+step i))=⟨i,true⟩)
lemma leaf_act (x:Site f)(b:Axis) (h:Odd T.count.val): (x,b)∈(planting T h).trunks ↔ seed (T.residue x) b := by
  rw [Forest.trunk_mem_iff]; have he : T.residue (x+step b)=T.residue x+step b:= by rw [map_add,← wrap_step f,T.residue_wrap,wrap_step]
  constructor
  · rintro ⟨u,hu,hp⟩; rcases H : steer (lift (T.residue u)) with ⟨a,z⟩; change (steer _).used _=_ at hp; rw [H] at hp
    cases z <;> simp only [Step.used] at hp
    · simp only [Bool.false_eq_true,↓reduceIte,Prod.mk.injEq] at hp; obtain ⟨rfl,rfl⟩:=hp; exact Or.inl ⟨(fallen _).mp hu,H⟩
    simp only [↓reduceIte,Prod.mk.injEq] at hp; obtain ⟨hp,g⟩:=hp; subst a
    have ht : u=x+step b:= by rw [← hp]; abel
    subst u; exact Or.inr (by rw [←he]; exact ⟨(fallen _).mp hu,H⟩)
  intro H; rcases H with ⟨hv,hv'⟩|⟨hv,hv'⟩
  · exact ⟨x,(fallen _).mpr hv,(by unfold planting; simp [hv',Step.used])⟩
  refine ⟨x+step b,(fallen _).mpr ?_,?_⟩
  · rwa [he]
  simp only [planting,he,hv',Step.used]; simp

-- expanded color slot keeping true count ℝ.
abbrev Dye (G:Gauge):= FreeResolvent.PAC G 1
abbrev Loose (G:Gauge)(L:Side):= {x:Co L (Dye G)// ¬ seed x.1 (axisEquiv.symm x.2.1)}
instance deckFinite (G:Gauge)(L:Side): Fintype (Loose G L):= Fintype.ofFinite _
def annex (c:Side)(p:Co c (Loose G L)): Co c (Co L (Dye G)):= (p.1,p.2.val)
lemma annex_mono (c:Side): Injective (annex (G:=G) (L:=L) c):= fun p q h=> Prod.ext (congr_arg (fun z:Co c (Co L (Dye G)) => z.1) h) (Subtype.ext (congr_arg (fun z:Co c (Co L (Dye G)) => z.2) h))
def bound (T:Ratio c f)(h:Odd T.count.val)(x:FreeResolvent.Active G (planting T h)): Co c (Loose G T.count) :=
    (T.parent x.1.val.1,⟨(T.residue x.1.val.1,(coord x.1.val.2,x.2)), fun he=> x.1.property (leaf_act (T:=T) x.1.val.1 x.1.val.2 h|>.mpr (by exact ((axisEquiv.symm_apply_apply x.1.val.2) ▸ he)))⟩)
lemma bound_prop (T:Ratio c f)(ho:Odd T.count.val)(x:FreeResolvent.Active G (planting T ho)): splitCo T (Dye G) (FreeResolvent.plant _ x) = annex c (bound T ho x):= by rw [split_co]; rfl
def aperture (T:Ratio c f)(ho:Odd T.count.val)(G:Gauge): FreeResolvent.Active G (planting T ho)≃ Co c (Loose G T.count):= Equiv.ofBijective (bound T ho) (by
  refine ⟨fun x y h=> FreeResolvent.plant_inj (planting T ho) ((splitCo T (Dye G)).injective ((bound_prop T ho _).trans ((congr_arg _ h).trans (bound_prop T ho _).symm))),?_⟩; rintro ⟨i, ⟨⟨u,y,a⟩,H⟩⟩
  let j:= axisEquiv.symm y; let x:=T.assemble (i,u); refine ⟨(⟨(x,j), by rw [leaf_act,T.assemble_res]; exact H⟩,a),?_⟩; refine Prod.ext (T.assemble_parent _) (Subtype.ext ?_); simp [bound,x]; exact axisEquiv.apply_symm_apply _)
lemma plant_free (T:Ratio c f)(h:Odd T.count.val)(G:Gauge)(x:FreeResolvent.Active G (planting T h)) : annex c (aperture T h G x) = splitCo T (Dye G) (FreeResolvent.plant (planting T h) x):= (bound_prop T h x).symm
end Larch
end YM.Pulse.Spine
