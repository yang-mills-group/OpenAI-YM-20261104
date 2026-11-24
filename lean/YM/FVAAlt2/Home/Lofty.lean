import YM.FVAAlt2.Shop.Match
import YM.FormalOPE.RG10.Position.Search
/-!
# At-for-Loft. Actual basis on each engineering weight.
Not a label identification post-horizon; choose one set of offshell lift representatives
 in the continuum Book to be precisely the same ones used in `begin`.
 Coefficient-handler linear maps for switching bases provided afterwards.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Home
open Function Finset Filter Topology Wilson Labels Source Source.Drops
open MS MS.Koszul MS.Native MS.Landau MS.Menus MS.Book MS.Cylinder MS.Cylinder.Taylor MS.Tone MS.Landau.Detect MS.Plane MS.Theater
open MS.Lifting MS.Local.Physical MS.Native.Paint MS.Native.Wilsonian
open Lattice Extra.FD Maxwell Extraction
open FormalOPE.RG10.Position (Loft Plan purity)
open Submodule
open scoped BigOperators Topology ContDiff
variable {G:Gauge}{d k:ℕ}{L:Frames G}(P:Loft L)(hP:P.Level L)
set_option quotPrecheck false
local notation "F"=> Labels.Label G d
local notation "ℜ" i=> (freeTable L).conj (table_spin L) i

def projector (P:Loft L)(d:ℕ) : Module.End ℂ (Label G d):= P.lift d ∘ₗ sourceAt L d
include hP in
lemma holds (x:(freeTable L).Field d): sourceAt L _ (P.lift d x)=x:= by apply writes_inj L d; rw [FormalOPE.RG10.Position.form,hP.warmth] -- include
-- assemble inductive unbiased choose all.
include hP in
lemma projects (x:F) : observable G d (projector P d x)=observable G d x:=by rw [projector,LinearMap.comp_apply,hP.warmth,FormalOPE.RG10.Position.form]
def projectsT (_L:Frames G)(d:ℕ)(k:ℕ) : Film0 G d k →ₗ[ℝ] Label G d:= ((Film0 G d k).subtype).codRestrict ((localFields G d).restrictScalars ℝ) (by intro i; obtain hs:=i.property; exact ⟨limitH hs.2, (cinema _|>.1 hs).2.1⟩)
abbrev kernelHouse (P:Loft L)(d k:ℕ): Submodule ℝ (Film0 G d k):= LinearMap.ker ((((projector P d) - LinearMap.id).restrictScalars ℝ) ∘ₗ (projectsT L d k))
lemma sunrise (x: Film0 G d k): x∈kernelHouse P d k↔ projector P d (projectsT L d k x) = projectsT L d k x:= LinearMap.mem_ker.trans sub_eq_zero
lemma early_v {p:F}(h: p∈ Grade (d,k))(hx:realBar p=p): p.val∈ Film0 G d k:= (cinema _).2 ⟨ (pure_grade ..).1 h,p.property.2, congr_arg Subtype.val hx⟩

def Soundly (P:Loft L)(d k:ℕ) : Submodule ℝ (Law G):= map ((orbit G).restrictScalars ℝ ∘ₗ (Film0 G d k).subtype) (kernelHouse P d k)
lemma SoundLe (d k:ℕ) : Soundly P d k≤ Allowed G d k:= by rintro u ⟨v,hv,rfl⟩; exact v.property.1
lemma op_real (x:Label G d): sourceAt L d (realBar x)= (ℜ d) (sourceAt L d x):= by apply writes_inj L d; rw [writes_bar,FormalOPE.RG10.Position.form, FormalOPE.RG10.Position.form,observe_bar] -- namespace
include hP
lemma SoundEq(d k:ℕ) : Soundly P d k⊔ MS.Local.Physical.Null G d k=Allowed G d k:= by
 apply le_antisymm (sup_le (SoundLe ..) (null_subset _)); intro u hu
 obtain ⟨p,hp,rfl⟩:= chooseX (r:=k) hu; let v:= projectsT L d k ⟨p,hp⟩; let q:= projector P d v; have hv : v∈Grade (d,k):= (pure_grade ..).2 (hp.2 : _); have ht: q.val∈ Film0 G d k:= early_v (p:=q) (hP.grade _ _ _ (FormalOPE.RG10.Position.form L d v |>.symm ▸ FormalOPE.RG10.Position.purity d (m:=(d,k)) v hv)) (by unfold q projector; rw [LinearMap.comp_apply,hP.form,← op_real v]; rw [show realBar v=v from Subtype.ext ((cinema _).mp hp).2.2]);
 have he : orbit G (p-q.val)∈ Null G d k:= by
    have hp': p-q.val∈ Film0 G d k:=sub_mem hp ht
    apply (certN hp'.2 hp'.1).mpr; rw [map_sub]; exact sub_eq_zero.mpr (Eq.symm (projects P hP v))
 refine mem_sup.mpr ⟨orbit G q.val, ⟨ ⟨ q.val,ht ⟩, ?_, rfl⟩, orbit G (p-q.val), he, by rw [map_sub]; abel⟩;  rw [SetLike.mem_coe,sunrise]; change projector P d q=q; unfold projector q; simp [projector,holds P hP]
lemma SoundB(d k:ℕ):Disjoint (Soundly P d k) (Null G d k):=by
 apply disjoint_def.mpr; rintro u ⟨v,hv,rfl⟩ h;  rw [SetLike.mem_coe,sunrise] at hv; have hh: sourceAt L _ (projectsT L d k v)=0:=by apply writes_inj L d; rw [FormalOPE.RG10.Position.form,map_zero]; exact (certN v.property.2 v.property.1).mp h
 change orbit G v.val=0; have he:(projectsT L d k v).val=v.val:=rfl; rw [← he,← hv, projector,LinearMap.comp_apply,hh,map_zero]; exact map_zero _

private abbrev aux (G:Gauge): Deck G:= Classical.choice (Deck.setting G)
def seats (P:Loft L)(hP:P.Level L):Deck G where
 carries d k:= match d with | .ofNat d => Soundly P d k| .negSucc v=> (aux G).carries (.negSucc v) k
 sup d k:=by cases d; exact SoundEq P hP _ _; exact (aux G).sup ..
 disjoint d k:=by cases d; exact SoundB P hP _ _; exact (aux G).disjoint ..
lemma loft_from(i:(seats P hP).BIndex d k): projector P d (Shop.seat (seats P hP) i)= Shop.seat (seats P hP) i:=by
 let B:= seats P hP; have h: orbit G (Shop.seat B i (d:=d)).val∈ Soundly P d k:= by change orbit G (film B (h:=d) i)∈_; rw [show orbit G _=B.raw _ _ i from lamp_here B i]; exact B.form d k i
 obtain ⟨p,hp,h⟩:= h; let x:=Shop.seat B i (d:=d); rw [show Shop.seat B i=projectsT L d k p from ?_]; exact (sunrise P p).1 hp
 exact Subtype.ext (opaqueL (pure_grade ..|>.1 (Shop.isSeated ..) : At x.val (d,k)) p.property.2 (Eq.symm h))
end YM.FVAAlt2.Home
