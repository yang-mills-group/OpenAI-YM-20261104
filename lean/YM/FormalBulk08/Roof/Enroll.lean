import YM.FormalBulk08.Roof.Attic

/-! Exact resulting normalized graph. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Roof
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {I J: Type*}{G:Gauge}{d m l e r D j t :ℕ}{K:KernelChoices}{F:Frame G d}{Y:Plaza F D}{o:Loc G 1}
lemma tribunal (Y:Plaza F D)(u:Letter F→ℝ)(o:Loc G 1)(hh:∀ i,Clef o (Y i) (slots F i))(hq:Colfax (slots F) (Pose.weight F) (pantry F Y) u):
    let S:=pantry F Y; let T:= larch Y S⁻¹
    Court o F T ∧ larch T S=Y:= by
    intro S T; refine ⟨⟨larch_cleared (slots F) (slots F) (hq.back.bound) hh,?_⟩,?_⟩
    · unfold T; rw [pantry_handle F _ (fun i=> (hh i).fare.through (slotsFits F i))]; exact Matrix.mul_nonsing_inv _ hq.det
    unfold T; rw [larch_circuit,Matrix.nonsing_inv_mul _ hq.det, larch_unit]

variable (F)(ρ:ChartRatio G)(a:hue G)(P:Flight j t)(V:Lodge P.patch)(h:P.patch.Branches K G)(hL: 2≤P.L.val)(W:Pot G)
variable (Y: Plaza F D) -- depends explicit

def pTrain : Tilework F:= pantry F (migrates a P V K W ρ h hL d d ∘ Y)
def avenue : Plaza F D:= larch (migrates a P V K W ρ h hL d d ∘ Y) (pTrain F ρ a P V h hL W Y)⁻¹
lemma axle (hp:Court o F Y)(hv:Story W (pink K.penalty P.wing))(hr:LocalRatio ρ)(H:Hol G)(he:d<D)(hd:d≤j)(ht:4≤t):
   Court o F (avenue F ρ a P V h hL W Y) ∧ larch (avenue F ρ a P V h hL W Y) (pTrain F ρ a P V h hL W Y)=migrates a P V K W ρ h hL d d ∘ Y := by
   let N:=migrates a P V K W ρ h hL d d ∘ Y; have hM:=performed o F Y ρ a P V h hL W H he hd ht hv hr hp; exact tribunal N _ o (fun i=>migrate_w a h hL d (hp.officers i) hv ht hr (slotsFits F _)) hM
-- matrix identities published. no hom props assumed on migrant.

lemma wadeCrow {I:Type*} (o:Loc G 1){u:ℕ}(S:Finset I)(T:I→Anthem D G)(h:∀ i∈S,Wade o (T i) u): Wade o (∑ i∈S,T i) u:= by
   induction S using Finset.induction with
   | empty=>rw [Finset.sum_empty]; exact wade_zero
   | insert i S he ih=> rw [Finset.sum_insert he]; exact (h i (Finset.mem_insert_self ..)).add (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))
lemma tally (o:Loc G 1){u:ℕ}(S:Finset I)(Y:I→ Anthem D G)(hy:∀ i∈S,Wade o (Y i) u)(hw:Story W (pink K.penalty P.wing))(hs:4≤t)(hr:LocalRatio ρ)(d:ℕ): migrates a P V K W ρ h hL d u (∑ i∈S,Y i)=∑ i∈S,migrates a P V K W ρ h hL d u (Y i):=by
   induction S using Finset.induction with
   | empty=>rw [Finset.sum_empty,Finset.sum_empty];exact migrant_zero a h hL d o u hw hs hr
   | insert i S he ih=>
      have hz(j)(hj:j∈S):=hy j (Finset.mem_insert_of_mem hj)
      rw [Finset.sum_insert he, Finset.sum_insert he,migrate_add a h hL d (hy i (Finset.mem_insert_self ..)) _ hw hs hr le_rfl, ih hz];
      exact wadeCrow o S Y hz
lemma hammers [Fintype I](o:Loc G 1)(d u:ℕ)(Y:I→ Anthem D G)(M:Matrix I J Pence)(hy:∀ i,Wade o (Y i) u)(hw:Story W (pink K.penalty P.wing))(hs:4≤t)(hr:LocalRatio ρ) : migrates a P V K W ρ h hL d u ∘ larch Y M=larch (migrates a P V K W ρ h hL d u ∘ Y) (M.map (Roof.reborn a P V K W ρ h)) := by
    funext x; unfold larch; rw [Function.comp_apply,tally _ _ P V h hL W o Finset.univ (fun j=>launch (M j x) (Y j)) (fun i _=> (hy i).launch _) hw hs hr]
    refine Finset.sum_congr rfl fun i _=> ?_ ; exact migrate_plus a h hL d (M i x) (hy i) hw hs hr le_rfl
end YM.FormalBulk08.Roof
