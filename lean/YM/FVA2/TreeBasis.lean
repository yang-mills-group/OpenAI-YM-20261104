import YM.FormalOPE.RG10.BlockGauge.Assembly
import YM.MS.Bare.Tangent

/-!
# Linear sliced charts and FP determinant convention

For the same quotient tree object that does actual multi-mark RG10 Haar/gauge elimination.
**Root is fixed**. Because the tree is only needed to identify the determinant/volume,
we work on the general setting of a finite step Loom. Include every link, even if some
path loops, to keep the volume rule. A normalization convention for every permissible
linear gauge slice is `L:Coordinates`: starts identical to tree coords modulo gradients.
This leaves only a common scale-independent determinant factor if one chooses other
 linear bases. Establish full determinant including the variable part in next file.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.TreeBasis
open FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open PertExtension MS MS.Bare MS.Bare.Maurer LinearMap Function Finset
open scoped Classical Topology ContDiff
variable {V E : Type} (G : Gauge)
abbrev Sites (V : Type) (G : Gauge) := V → G.Color
abbrev Links (E : Type) (G : Gauge) := E → G.Color
abbrev Nonroot (D : Loom V E) := { v : V // v ≠ D.origin }
abbrev Root (D : Loom V E) (G : Gauge) := Sites (Nonroot D) G
abbrev Free {D : Loom V E}(T : D.Truss) (G : Gauge) := Links T.Bulk G

-- Keep Classical propDecidable implicit consistent across calls using `[Fintype V/E]` only.
def guarded (D : Loom V E) : Root D G →ₗ[ℝ] Sites V G :=
  LinearMap.pi fun v => if h:v=D.origin then 0 else LinearMap.proj (Subtype.mk v h : Nonroot D)

@[simp] lemma guard_zero (D : Loom V E) (p : Root D G) : guarded G D p D.origin=0:= by simp [guarded]
@[simp] lemma guard_off (D : Loom V E) (p : Root D G) (i: Nonroot D) : guarded G D p i.val=p i:= by simp [guarded,i.property]
lemma guarded_inj (D : Loom V E) : Injective (guarded G D):= fun a b e => funext (fun i => (guard_off G D a i).symm.trans ((congr_fun e i.val).trans (guard_off G D b i)))

/-- Site log algebra acting on links. Follow Manuscript and MS.Bare inverse gauge convention. -/
def turn (D : Loom V E) (A : Links E G) : Sites V G →ₗ[ℝ] Links E G :=
  LinearMap.pi fun i => (voltage (A i)).comp ((LinearMap.proj (D.fromEdge i)).prod (LinearMap.proj (D.toEdge i)))

def directed (D : Loom V E) (A : Links E G) : Root D G →ₗ[ℝ] Links E G := turn G D A ∘ₗ guarded G D
abbrev d (D : Loom V E) := directed G D 0

lemma moves (D : Loom V E) (A : Links E G) (a : Sites V G) (i:E):
    turn G D A a i= Maurer.voltage (A i) (a (D.fromEdge i),a (D.toEdge i)):= rfl
lemma at_origin (D : Loom V E) (A : Links E G) (a : Sites V G) (i:E) (h:A i=0) :
    turn G D A a i= a (D.toEdge i)-a (D.fromEdge i) := by rw [moves,h]; exact volt_zero _
lemma diff (D : Loom V E) (p : Root D G) (i : E): d G D p i = guarded G D p (D.toEdge i)-guarded G D p (D.fromEdge i):= at_origin G D _ (guarded G D p) i rfl

variable {D : Loom V E} (T : D.Truss)

/-- The rooted infinitesimal gauge directions inject into the tree link space. -/
def detour : Root D G →ₗ[ℝ] Links T.Tree G := LinearMap.pi fun i=> LinearMap.proj i.val ∘ₗ d G D

lemma detour_inj : Injective (detour G T):= by
  apply ker_eq_bot.mp; apply bot_unique; intro u hu; have he : detour G T u=0:=hu
  have hz : ∀ v : V,guarded G D u v=0:= by
     intro v; induction hk : T.height v using Nat.strong_induction_on generalizing v with
     | h n ih =>
       by_cases h:v=D.origin
       · subst v; simp
       let i:=T.wire v h
       have hv: d G D u i=0:= congr_fun he ⟨i,T.wire_branch v h⟩
       rw [diff] at hv; have hp: guarded G D u (T.parent v h)=0:= ih _ ((T.descend v h).trans_eq hk) _ rfl
       rcases T.orientation v h with ⟨h,hx⟩|⟨h,hx⟩ <;> (unfold i at hv; rw [h,hx, hp] at hv) -- potential h shadows name
       · simpa using hv
       simpa using hv
  exact (Submodule.mem_bot _).mpr (guarded_inj G D (Eq.trans (funext hz : guarded G D u=0) (map_zero _).symm))

include T in
lemma d_inj : Injective (d G D):= fun _ _ h=> detour_inj G T (funext fun i=> congr_fun h i.val)

variable [Fintype V][Fintype E]

def pairs : Nonroot D ≃ T.Tree := Equiv.ofBijective (fun x : Nonroot D=> (⟨T.wire x.val x.property,T.wire_branch ..⟩:T.Tree))
      ⟨fun a b he=> Subtype.ext (T.distinguish _ _ _ _ (Subtype.mk.inj he)),fun i=> by
        obtain ⟨e,v,h,rfl⟩:=i; exact ⟨⟨v,h⟩,rfl⟩ ⟩

def treeIso : Root D G ≃ₗ[ℝ] Links T.Tree G :=
   LinearEquiv.ofBijective (detour G T) ⟨ detour_inj G T, (injective_iff_surjective_of_finrank_eq_finrank
       ((LinearEquiv.piCongrLeft ℝ (fun _=> G.Color) (pairs T)).finrank_eq)).mp (detour_inj G T) ⟩


def pick : Links E G →ₗ[ℝ] Links T.Tree G := LinearMap.pi fun i=> LinearMap.proj i.val
lemma picks (v : Root D G) : pick G T (d G D v)=treeIso G T v:=rfl

def enter : Free T G →ₗ[ℝ] Links E G := LinearMap.pi fun i=> if h:T.Branch i then 0 else LinearMap.proj (Subtype.mk i h : T.Bulk)
def restrict : Links E G →ₗ[ℝ] Free T G := LinearMap.pi fun i=> LinearMap.proj i.val
omit [Fintype V] [Fintype E] in
lemma full {a b : Links E G} (h:pick G T a=pick G T b)(hp:TreeBasis.restrict G T a=TreeBasis.restrict G T b): a=b:= funext fun i => (Classical.em (T.Branch i)).elim (fun hi=> congr_fun h (⟨i,hi⟩:T.Tree)) (fun hi=> congr_fun hp (⟨i,hi⟩:T.Bulk))
omit [Fintype V] [Fintype E] in
lemma enter_v (u : Free T G) (i : E) : enter G T u i = T.stitch 0 u i:= by
    by_cases h : T.Branch i <;> simp [enter,Loom.Truss.stitch,h]
omit [Fintype V] [Fintype E] in
lemma entry (u : Free T G) : pick G T (enter G T u)=0 := funext fun i=> (enter_v G T u i.val).trans (T.stitch_tree ..)
omit [Fintype V] [Fintype E] in
lemma entry_back (u : Free T G) : TreeBasis.restrict G T (enter G T u)=u := funext fun i=> (enter_v G T u i.val).trans (T.stitch_bulk ..)
omit [Fintype V] [Fintype E] in
lemma entry_exp (u : Free T G) : PertExtension.Chart.expLinks G _ (enter G T u)=T.board (PertExtension.Chart.expLinks G _ u):= by
    ext1 i; by_cases h:T.Branch i <;> simp [enter,Loom.Truss.board,Loom.Truss.stitch,Chart.expLinks,h]

def split (A : Links E G) : Root D G × Free T G →ₗ[ℝ] Links E G := coprod (directed G D A) (enter G T)
omit [Fintype V] [Fintype E] in
lemma split_tree (A : Free T G) (p : Root D G) (i : T.Tree) : pick G T (directed G D (enter G T A) p) i=detour G T p i:= by change turn G D _ _ i.val=d G D _ i.val; rw [at_origin G D (enter G T A) _ i.val (congr_fun (entry G T A) i), diff]

-- explicit inverse, also for nonzero B (on tree-gauge subspace)
def axes (B : Free T G) : (Root D G × Free T G) ≃ₗ[ℝ] Links E G where
  toFun := TreeBasis.split G T (enter G T B)
  invFun := fun A => let p:=(treeIso G T).symm (pick G T A); (p, TreeBasis.restrict G T (A - directed G D (enter G T B) p))
  left_inv := by
     rintro ⟨p,b⟩
     let f:Root D G→ₗ[ℝ] Links E G:= directed G D (enter G T B)
     change (((treeIso G T).symm (pick G T (f p+enter G T b))), _)=(p,b)
     have hm: (treeIso G T).symm (pick G T (f p+enter G T b))=p:= by rw [map_add,entry,add_zero, show pick G T (f p)=treeIso G T p from funext (split_tree G T B p),LinearEquiv.symm_apply_apply]
     apply Prod.ext hm; change TreeBasis.restrict G T (f p+enter G T b-f ((treeIso G T).symm (pick G T (f p+enter G T b))))=b; rw [hm,add_comm (f p),add_sub_cancel_right, entry_back]
  right_inv := by
     intro A; let p:=(treeIso G T).symm (pick G T A); let f:=directed G D (enter G T B); let t:= TreeBasis.restrict G T (A-f p); change f p+enter G T t=A
     apply full G T
     · rw [map_add, entry, add_zero, show pick G T (f p)=treeIso G T p from funext (split_tree G T B p)]
       exact LinearEquiv.apply_symm_apply _ _
     rw [map_add,entry_back]; unfold t; rw [map_sub]; abel
  map_add' := map_add _
  map_smul' := map_smul _

lemma charges (B : Free T G) (p : Root D G) (v: Free T G) : axes G T B (p,v)=directed G D (enter G T B) p + enter G T v:= rfl
abbrev whereL : Links E G →ₗ[ℝ] Free T G := LinearMap.snd ℝ _ _ ∘ₗ (axes G T 0).symm.toLinearMap
lemma where_exp (A : Links E G) : ∃ p:Root D G,d G D p+enter G T (whereL G T A)=A :=
  ⟨ ((axes G T 0).symm A).1,by rw [← show directed G D (enter G T 0)=d G D from by rw [map_zero], ← charges]; exact LinearEquiv.apply_symm_apply (axes G T 0) A⟩
lemma where_apply (p : Root D G) (b:Free T G) : whereL G T (d G D p+enter G T b)=b:= by
     rw [← show directed G D (enter G T 0)=d G D from by rw [map_zero], ← charges]; unfold whereL; simp


-- equivalent generation all linear slices and FP det convention
structure SectionBasis (D : Loom V E) (T : D.Truss) (G : Gauge) [Fintype V][Fintype E] where
  L : Free T G →ₗ[ℝ] Links E G
  agreement (b : Free T G) : whereL G T (L b)=b

variable {G T}
namespace SectionBasis
variable (Z : SectionBasis D T G)
lemma d_where (p : Root D G) : whereL G T (d G D p)=0 := by simpa using where_apply G T p 0

def full (Z : SectionBasis D T G) (b : Free T G) := coprod (directed G D (Z.L b)) Z.L
lemma full_at_zero (p : Root D G) (b : Free T G) : full Z 0 (p,b) = d G D p+Z.L b:= by unfold full d; rw [map_zero]; rfl
def equiv (Z : SectionBasis D T G) : (Root D G × Free T G) ≃ₗ[ℝ] Links E G := LinearEquiv.ofBijective (Z.full 0) (by
    suffices h:Injective (Z.full 0) from ⟨h,(injective_iff_surjective_of_finrank_eq_finrank (axes G T 0).finrank_eq).mp h⟩
    intro a b he; rcases a with ⟨a,x⟩; rcases b with ⟨b,y⟩; simp_rw [full_at_zero] at he
    have hx:= congr_arg (whereL G T) he; simp_rw [map_add,d_where,Z.agreement,zero_add] at hx; subst y
    rw [d_inj G T (add_right_cancel he)] )
lemma equiv_acts (p : Root D G) (b : Free T G) : Z.equiv (p,b) = d G D p+ Z.L b := full_at_zero Z p b
lemma equiv_right (A : Links E G) : (Z.equiv.symm A).2 = whereL G T A := by
    obtain ⟨⟨p,b⟩,rfl⟩:=Z.equiv.surjective A
    rw [LinearEquiv.symm_apply_apply,equiv_acts,map_add,d_where,Z.agreement,zero_add]
def projection (Z:SectionBasis D T G) : Links E G→ₗ[ℝ] Root D G:= LinearMap.fst ℝ _ _ ∘ₗ Z.equiv.symm.toLinearMap
lemma in_zero (p : Root D G) : Z.projection (d G D p)=p:= by
     have h: Z.equiv (p,0)=d G D p:=by rw [equiv_acts,map_zero,add_zero]
     change (Z.equiv.symm _).1=p; rw [← h,LinearEquiv.symm_apply_apply]
lemma in_slice (b : Free T G) : Z.projection (Z.L b)=0:= by
     have h: Z.equiv (0,b)=Z.L b:=by rw [equiv_acts,map_zero,zero_add]
     change (Z.equiv.symm _).1=_; rw [← h,LinearEquiv.symm_apply_apply]
lemma resolves (A : Links E G) : d G D (Z.projection A)+Z.L (whereL G T A)=A:= by
     rw [← Z.equiv_right,← equiv_acts]; exact LinearEquiv.apply_symm_apply Z.equiv A

def ghosts (Z:SectionBasis D T G) (b : Free T G) : Root D G →ₗ[ℝ] Root D G:=
    Z.projection.comp (directed G D (Z.L b))

def fpdet (Z: SectionBasis D T G) (u: Free T G):ℝ:= LinearMap.det (ghosts Z u)
lemma ghosts_zero : Z.ghosts 0 = LinearMap.id:= by
     apply LinearMap.ext; intro x; unfold ghosts; rw [map_zero,LinearMap.comp_apply]; exact in_zero Z x
lemma price_one : Z.fpdet 0=1:= by rw [fpdet,ghosts_zero,det_id]

end SectionBasis
end YM.FVA2.TreeBasis
