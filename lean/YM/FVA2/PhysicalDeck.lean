import YM.FVA2.LiftedLabels
import YM.Pert.Lattice.Lifts
import YM.X.Bare.Uncut
/-!
# Using the prescribed closest free-label lifts on the two hierarchies

The dual is signed-turn compatible, real, dimension and slot graded. Used
at own horizon and nested. Not before pole subtractions.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
namespace YM.FVA2.ColorCode
open Filter Topology Set Function Submodule
open Pert Pert.RawLabels Pert.Position PositionX Maxwell Maxwell.Free
open Lattice Labels
open MS MS.Local.Physical MS.Menus MS.Theater MS.Landau MS.Landau.Detect
open scoped Topology Classical ContDiff
variable {G:Gauge} (F:Frames G) {d r u v:ℕ}
local notation "pκ"=> rebase G

def rotor (G:Gauge)(d r:ℕ) : Submodule ℝ (Law G) := Submodule.map ((Theater.orbit G).restrictScalars ℝ) (Submodule.map ((changed (rebase G)).toLinearMap.restrictScalars ℝ) (Film0 G d r))
lemma activeM {p:Labels.Pol G}(h:p∈ Film0 G d r): changed (rebase G) p∈ Film0 G d r:= by
   obtain hh:= (cinema _).mp h; let P : Label G d:= ⟨p, limitH hh.1,hh.2.1⟩
   refine (cinema _).mpr ⟨ still (rebase G) hh.1,(fixedPolynomial G d P).property.2,?_⟩; have he : realBar P=P:=Subtype.ext hh.2.2; exact (congr_arg Subtype.val ((fixed_real P).trans (congr_arg _ he)))
lemma rotor_le : rotor G d r ≤ Allowed G d r:= by rintro f ⟨_,⟨p,h,rfl⟩,rfl⟩; exact (activeM h).1
lemma rotor_none (f:Law G)(h:f∈rotor G d r)(hf:f∈Null G d r): f=0:= by
    obtain ⟨_,⟨p,h,rfl⟩,rfl⟩:=h; obtain ht:= (certN (activeM h).2 (activeM h).1).mp hf; change reduceEq (changed _ p)=0 at ht; rw [unchanged] at ht; change Theater.orbit G (changed (rebase G) p)=_; rw [convertPol (G:=G),ht,map_zero,map_zero]
lemma rotor_rest : rotor G d r ⊔ Null G d r = Allowed G d r := by
    refine le_antisymm (sup_le rotor_le (null_subset G)) ?_; intro f h; obtain ⟨p,hp,rfl⟩:= chooseX h
    let X:= changed pκ p; let V:= orbit G X; refine Submodule.mem_sup.mpr ⟨ V,⟨_,⟨p,hp,rfl⟩,rfl⟩, (Theater.orbit G p-V),?_,by abel⟩
    unfold V; rw [← map_sub]; have he := (Film0 G d r).sub_mem hp (activeM hp); exact (certN he.2 he.1).mpr (by rw [map_sub,show reduceEq X=reduceEq p from unchanged p,sub_self])
-- handle negative int.D lower empty
def wings (G:Gauge): Deck G where
   carries i r:= if 0 ≤ i  then rotor G i.toNat r else (Classical.choice (Deck.setting G)).carries i r
   sup i r:= by
               split; swap; exact (Classical.choice .. : Deck G).sup _ _
               next hi=> lift i to ℕ using hi; simpa only [Int.toNat_natCast] using (rotor_rest (G:=G) (d:=i) (r:=r))
   disjoint i r:= by
       split
       · next hi=> lift i to ℕ using hi; rw [Int.toNat_natCast]; exact disjoint_def.mpr fun f hv he=> rotor_none _ hv he -- disjoint lemma
       exact ( Classical.choice (Deck.setting G)).disjoint i r
private lemma wings_mem : (wings G).carries d r=rotor G d r:=by unfold wings; dsimp
local notation "B"=> wings G
lemma label_t (i: (B).BIndex d r) : fixedPolynomial G d (Warehouse.label (wings G) d r i)= Warehouse.label (wings G) d r i:= by
    let p:=film B i (h:=d); obtain h:= (B).form d r i; rw [wings_mem,← lamp_here (wings G) i] at h; obtain ⟨_, ⟨y,h,rfl⟩,hk⟩:= h; have he:= opaqueL (p:= (changed pκ y)) (q:=p) ((cinema _).mp (activeM h)|>.1) ((cinema _).mp (filmW B i)|>.1) hk; apply Subtype.ext; change changed pκ p=p; rw [← he, flat_idem]

open Extra.FD (exactField rideO writes writes_unit)
open MS.Local.Physical MS.Menus

abbrev BasisIx (G:Gauge) (d:ℕ) := Glyph (wings G) d
def sameAxis (d:ℕ) : Module.Basis (BasisIx G d) ℂ (E F d):= (Daylight B d).map (exactField F d).symm
def letter (u:BasisIx G d) : Label G u.size:= Warehouse.label B u.size u.grade u.2.2
lemma not_under (i:BasisIx G d) : i.size≤d:= Nat.le_of_lt_succ i.1.isLt
lemma physical_letter (i:BasisIx G d): physicalLabel F d (sameAxis F d i)=raiseLabel G (not_under i) (letter i):= by
   let v:= raiseLabel G (not_under i) (letter i)
   suffices H: sameAxis F d i=enroll F d v by rw [H,embed_round,fixed_includes, show fixedPolynomial G i.size (letter i)=letter i from label_t i.2.2]
   apply (exactField F d).injective; rw [sameAxis,Module.Basis.map_apply,LinearEquiv.apply_symm_apply, readHeight]; apply Subtype.ext; symm; change writes F d ((freeTable F).project d ((F.level d).coords v))= _; rw [Extra.FD.writes_project]; apply (congr_arg (fun z:Label G d=> reduceEq z.val) ((F.level d).coords.symm_apply_apply v))
lemma genuine (i:BasisIx G d): writes F d (sameAxis F d i)=Letters (wings G) i:= by
   unfold sameAxis writes; rw [Module.Basis.map_apply]; change (exactField _ _ _).val=_; rw [ (exactField F d).apply_symm_apply, readHeight ]
def includeI (B':Deck G) {u v:ℕ} (h:u≤v) (i:Glyph B' u): Glyph B' v:= ⟨⟨ i.size,Nat.lt_succ_of_le ((Nat.le_of_lt_succ i.1.isLt).trans h)⟩,i.2⟩
def labelAt (B':Deck G) {u:ℕ} (i:Glyph B' u): Rake.Label B' := ⟨ i.size,i.2 ⟩
lemma same_up (h:u≤v)(i:BasisIx G u): up F h (sameAxis F u i)= sameAxis F v (includeI (wings G) h i):= by
   apply physical_inj; simp_rw [up, physical_inclusion F (scheme_filters F), physical_letter]; rfl
lemma graded (i:BasisIx G d): physicalLabel F d (sameAxis F d i)∈ Labels.Grade (i.size,i.grade):= by rw [physical_letter]; exact Warehouse.label_grade B i.2.2
lemma conj_basisX (i:BasisIx G d): (Model F).conj (hierarchy F).spin d (sameAxis F d i)=sameAxis F d i:= by apply physical_inj; simp_rw [physical_real,physical_letter]; apply Subtype.ext; exact congr_arg (fun x:Label G i.size=>x.val) ( Warehouse.label_real B (d:=i.size) i.2.2 )
end YM.FVA2.ColorCode
