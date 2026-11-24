import YM.Contacts.Ion.Harps
namespace YM.Contacts.Lyre
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie Harrier Sequent
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k i r l j M D:ℕ}{ζ σ:ℝ≥0}
open UVNext PricedKernels Next.Free Lattice Tree FreeResolvent
open PertExtension.Orb MeasureTheory
namespace Align
-- orbit tree presence. internal roots with fixed sites fine can't be leaves. exposure for joint multilevel integration.
variable {f:Side}(S:StepData m f)
abbrev Forestry := planting S.ratio S.patch.odd_side
lemma pupil (x:Site f): Tree.leaf S.ratio (-x)↔ Tree.leaf S.ratio x:= by rw [Larch.fallen,Larch.fallen,map_neg]; simp only [ne_eq,neg_eq_zero]
lemma contour (x:Site f)(he:Tree.leaf S.ratio x): (Forestry S).up (-x)= ((Forestry S).up x).rev:= by
   have hL:= S.patch.odd_side; let y:= S.ratio.residue x; have hp:y≠0:= (Larch.fallen ..).mp he;
   change steer (lift (S.ratio.residue (-x))) = _; rw [map_neg,Larch.plank S.ratio.count hL]; apply (stake (lift y) (?_)); intro he; exact hp (by rw [←wrap_lift y,he,map_zero])
lemma trunk (u:SLink f) : reflect u∈ (Forestry S).trunks ↔ u∈(Forestry S).trunks:= by
   let p:= Forestry S; have ht (u:SLink f)(he:u∈p.trunks): reflect u ∈ p.trunks:= by obtain ⟨x,hx,rfl⟩:= (p.trunk_mem_iff _).mp he; let H:p.up (-x)=(p.up x).rev:= contour S x hx; exact (p.trunk_mem_iff _).mpr ⟨-x,(pupil S x).mpr hx,H.symm ▸ (used_flip (p.up x) x)⟩
   exact ⟨fun h=> reflect_reflect u▸ht _ h, ht u⟩
private lemma sound_read {V:Config G f}(h:Halo V) (a:Lattice.Step) (x:Site f): a.rev.read V (-x)=a.read V x:= by
   unfold Step.read; rw [used_flip,h]; rcases a with ⟨i,v|v⟩ <;> simp [Step.rev]
lemma lantern {V:Config G f}(h:Halo V) : ∀ x:Site f,(Forestry S).foldAt V (-x)=(Forestry S).foldAt V x:= by
   intro x; let p:=Forestry S; induction x using Tree.Forest.hike.induct p with
   | case1 x hx ih =>
       apply mul_right_cancel (b:=(p.up x).read V x); rw [show _ * _= _ from p.fold_step V hx]; rw [← sound_read h,← contour S x hx,p.fold_step V ((pupil S x).mpr hx)]; rw [show -x + (p.up (-x)).vec = -(x+(p.up x).vec) from ?_,ih]; rw [show p.up (-x) = (p.up x).rev from contour S x hx,Step.vec_rev,neg_add]
   | case2 x hx =>
       have hh x (hx:¬ Tree.leaf S.ratio x): p.foldAt V x=1:= by rw [show x=_ from (Classical.not_not.mp hx:x=S.ratio.embed (S.ratio.parent x)),p.fold_root]; -- cast
       exact (hh (-x) (mt (pupil S x).1 hx)).trans (hh x hx).symm
-- true peelings to quotient gauges at each step. no extra factor
abbrev Bark := {x:orb f// x.val ∈(Forestry S).trunks}
abbrev Rem := {x:orb f// x.val ∉(Forestry S).trunks}
def path : Entry G f ≃ᵐ ((Bark S→G.El)×(Rem S→ G.El)):= MeasurableEquiv.piEquivPiSubtypeProd _ _
lemma slip_in (a:Bark S→ G.El)(b: Rem S→ G.El)(x:Bark S): (path S).symm (a,b) x.val=a x:= congr_fun (congr_arg Prod.fst ((path S).apply_symm_apply (a,b))) x
lemma slip_out (a:Bark S→ G.El)(b: Rem S→G.El)(x:Rem S): (path S).symm (a,b) x.val=b x:= congr_fun (congr_arg Prod.snd ((path S).apply_symm_apply (a,b))) x
-- hold at internal centers under gauge
lemma frame_eq (x y : Entry G f)(h:∀ i:Bark S,x i.val=y i.val):(Forestry S).foldAt (liftLinks x)=(Forestry S).foldAt (liftLinks y):= by
   apply Tree.Forest.names; intro z hz; let u:=PertExtension.Orb.index z; have hx:eR z ∈ (Forestry S).trunks:=(eR_spec z).elim (fun he=> he.symm ▸ hz) (fun he=>he.symm ▸ (trunk S z).mpr hz); simp_rw [liftLinks, show x (PertExtension.Orb.index z)=y u from h (⟨u,hx⟩:Bark S)]; rfl -- error cast
end Align
end
end YM.Contacts.Lyre
