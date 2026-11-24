import YM.MergeProof.North.Fermi

/- Generalization of YM/MergeProof/North/Fermi. Propagation with
   a genuinely shared per-copy program over *all* finitely many active
   insertions, and same coherences on all internal modes. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Canopies
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V][Fintype V] {feathers : Type}[DecidableEq feathers][Fintype feathers] {n:Side}{G:Gauge}{B:Census V}
open Extra.Histories Push Push.Local Motion
abbrev Live (V feathers:Type*):= V × feathers
abbrev Now (V feathers:Type*)[DecidableEq V][Fintype V][DecidableEq feathers][Fintype feathers] := Bud (Live V feathers)
def spotlight (p:(Now V feathers).Mode) : (Bud V).Mode := ⟨p.val.image Prod.fst,mem_univ _⟩
lemma spotlights (i:(Now V feathers).Mode)(j) : j∈(spotlight i).val ↔ ∃ k,(j,k)∈i.val:=by simp [spotlight,eq_comm]
variable (b: Equiv.Perm V)
def nome : Equiv.Perm (Live V feathers):= Equiv.prodCongr b (Equiv.refl _)
def pars (B:Equiv.Perm V):Equiv.Perm (Bud V).Mode where
    toFun p:=⟨p.val.image B,mem_univ _⟩
    invFun p:=⟨p.val.image B.symm,mem_univ _⟩
    left_inv p:=Subtype.ext (by simp [image_image])
    right_inv p:=Subtype.ext (by simp [image_image])
lemma pares (i:(Bud V).Mode): (pars b i).val=i.val.image b:=rfl
def drum : Equiv.Perm (Now V feathers).Mode := pars (nome b)
lemma recall (i:(Now V feathers).Mode): spotlight (drum b i)=pars b (spotlight i):=Subtype.ext (by unfold spotlight; simp only [drum,pares,image_image];rfl)
def Focused (v:V)(p:(Now V feathers).Mode):Prop:= (spotlight p).val⊆ {v}
lemma going (v:V)(p:(Now V feathers).Mode): Focused v p ↔ Focused (b v) (drum b p):=by
    unfold Focused; rw [recall,pares,← image_singleton b]; exact (Finset.image_subset_image_iff b.injective).symm
lemma go_one (p:Live V feathers) : drum b ((Now V feathers).fire p)=(Now V feathers).fire (nome b p):= Subtype.ext (by unfold drum; rw [pares];exact image_singleton ..)
lemma which (v:V)(p:Live V feathers):Focused v ((Now V feathers).fire p) ↔ p.1=v:=by simp [Focused,Census.fire,spotlight]

lemma extends_on [Fintype I]{p q : I→Prop}{f:{i//p i}→{i// q i}}(he:Bijective f) : ∃ k:Equiv.Perm I,(∀ i:{i//p i}, k i.val=(f i).val) ∧ ∀ i,p i ↔ q (k i):=by
    let B:= Equiv.ofBijective f he; refine ⟨Equiv.extendSubtype B,fun i=> Equiv.extendSubtype_apply_of_mem B i.val i.property,fun i=>⟨fun hi=>Equiv.extendSubtype_mem B i hi,fun hi=> not_not.mp (fun he=> Equiv.extendSubtype_not_mem B i he hi)⟩⟩
end YM.MergeProof.Canopies
