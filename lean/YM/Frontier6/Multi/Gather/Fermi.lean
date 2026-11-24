import YM.MergeProof.North.Fermi
import YM.MergeProof.North.Harbor
import YM.Frontier6.Multi.Gather.Palate

/- Generalization of MergeProof/North/Fermi to complete reaping and preservation of
   copy charts on whole internal modes after a partial grouping. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Canopies
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V][Fintype V]{A₁ A₂:Type}[DecidableEq A₁][DecidableEq A₂][Fintype A₁][Fintype A₂]{π:Concentrate A₁ A₂} {n:Side}{G:Gauge}{B:Census V}
open Extra.Histories Push Push.Local Motion
variable (π) (b: Equiv.Perm V)

def batt (π: Concentrate A₁ A₂) : Concentrate (Live V A₁) (Live V A₂):=⟨Prod.map id π.hit, Prod.map id π.seat,fun ⟨i,j⟩=> Prod.ext rfl (π.parked j)⟩
lemma attends (p:(Now V A₁).Mode): (batt (V:=V) π).span (drum b p) = drum b ((batt (V:=V) π).span p):= by
   apply Subtype.ext; unfold Concentrate.span; simp only [drum,pares,image_image]; rfl
lemma plena (p:(Now V A₂).Mode): (batt (V:=V) π).plena (drum b p)=drum b ((batt π).plena p):=by
   apply Subtype.ext; ext1 i; obtain ⟨i,rfl⟩:= (nome b).surjective i
   unfold Concentrate.plena; simp only [drum,pares,mem_filter,mem_univ,true_and,Ribbons.mem_image_of_injective _ (nome b).injective] -- alias mem_image
   rw [show (batt π).hit (nome b i)=nome b ((batt π).hit i) from rfl]
   exact (Ribbons.mem_image_of_injective _ (nome b).injective)
lemma garner (j:(Now V A₁).Mode):(batt π).Pays j↔ (batt π).Pays (drum b j):=by
   unfold Concentrate.Pays; rw [attends,plena,(drum b).apply_eq_iff_eq]
omit b in
lemma bands (v:V)(p:(Now V A₁).Mode) : Focused v ((batt π).span p) ↔ Focused v p:=by
   have he:spotlight ((batt π).span p)=spotlight p:= Subtype.ext (by unfold spotlight Concentrate.span; simp only [image_image]; rfl)
   exact iff_of_eq (congr_arg (fun i:(Bud V).Mode=>i.val⊆ {v}) he)
variable {π}
variable (Z: Salt (batt (V:=V) π) G n)
structure Twin (z : ℝ) (m:Motion)(x:Site n)(v u:V) (b:Equiv.Perm V) : Prop where
   who : b v=u
   ways i : Z.grain (u,i) = affine m.1 x (Z.grain (v,i))
   debut i: Z.pepper (u,i)= scalar m (Z.pepper (v,i))
   kin p (hp:Focused v p) i U: (Z.air (MergeProof.sky m x i) U).part (drum b p)=scalar m ((Z.air i (pull m.1 x U)).part p)
   jets p (hp:Focused v p) i U:(Z.river (puff m x i) U).part (drum b p)= scalar m ((Z.river i (pull m.1 x U)).part p)
variable {t:ℝ}{m: Motion}{x:Site n}{v u:V}
local notation "E"=> Equiv.Perm
namespace Twin
variable {Z b}
variable (h:Twin Z t m x v u b)
include h
lemma goes (i:(Now V A₁).Mode) : Focused v i↔ Focused u (drum b i):=by rw [←h.who]; exact going ..
lemma homes (i:(Now V A₁).Mode)(hp:Focused v i)(p:Support n) : i.val.image Z.grain⊆ p↔ (drum b i).val.image Z.grain ⊆ sky m x p:=by
   have he:(drum b i).val.image Z.grain=(i.val.image Z.grain).image (turnSites m.1 x):=by
      unfold drum; rw [pares,image_image,image_image]; apply Finset.image_congr; rintro ⟨k,j⟩ hj; have hh : k=v:=mem_singleton.mp (hp (mem_image_of_mem _ hj)); subst k; change Z.grain (b _,_)=_; rw [h.who]; exact h.ways _
   rw [he,shading]; exact (Finset.image_subset_image_iff (turnSites m.1 x).injective).symm
lemma kilo (i:(Now V A₁).Mode)(hp:Focused v i)(p:Support n): Z.kiln (sky m x p) (drum b i)=sky m x (Z.kiln p i):=by
    unfold Salt.kiln; rw [attends,drum,pares,shading,shading,image_union,image_image,image_image]; refine congr_arg (_ ∪ ·) (Finset.image_congr ?_);
    rintro ⟨i,B⟩ hi; have hh:= (bands π v _).2 hp; have hz:i=v:=mem_singleton.mp (hh (mem_image_of_mem Prod.fst hi)); subst i; change Z.grain (b v,π.seat B)=_; rw [h.who]; exact h.ways _
end Twin
end YM.MergeProof.Canopies
