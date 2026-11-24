import YM.RG05Readout.Records.Packet
/-!
# Assign product markers, Census policy with all simultaneous groups in cameras

Indices `V` of centers at level n+1 (o→I); assignment to real copies from
colors. Displacements arbitrary within Cover constraints checked later. `W`
lower allocation is full Bud on real copies; each commits at most one branch
or its counter. Before projection (on the last group step) choose any permitted
many product polynomial on that single-branch cluster. No same-mode pairs of
different branches for that COPY, polynomial still complete after grouping.
Costs can pay full occupancy enlarged in receipts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Records
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}{W V J I:Type}[DecidableEq V][Fintype V][DecidableEq J][Fintype J][DecidableEq I][Fintype I] [DecidableEq W][Fintype W]
set_option quotPrecheck false
local notation "X!"=>C.side N p
open Ribbons Ribbons.ManyCopies

/- publisher: J columns at capture, I actual copy. r assigns colors. -/
namespace Basket
abbrev Color (V:Type):= Option V ⊕ Unit
abbrev Recipe (J V:Type):= J × Color V
abbrev Root (J:Type):= J × Bool
local notation "T"=> Recipe J V
local notation "T₁"=> Root J
local notation "L"=> Unit × Recipe J V
local notation "L'"=> Unit × Root J
abbrev producer (i:V): Color V:=Sum.inl (some i)
abbrev center (V:Type): Color V:=Sum.inl none
abbrev counter (V:Type): Color V:=Sum.inr ()
abbrev fire (x:T):T₁ := (x.fst,x.snd.isLeft)
def basin (J V:Type):Fibers (Recipe J V) (Root J) where
    bunch:= fire
    twig b:= (b.fst,if b.snd then center V else counter V)
    sectioned := by rintro ⟨x,b⟩;cases b<;> rfl
local notation "Λ"=> basin J V
local notation "Π"=>partialGroup Unit (basin J V)
-- decentralized phrase: inject into output copy only at whole group
variable (c:J→I)
local notation "ξ"=> Π.bunch
local notation "pλ"=> (fun i:L' => c i.snd.fst)
-- permission.Before group. colored record. Normalize via pelvis
abbrev Clan (X:Finset (Unit×Recipe J V)) := ∀ i∈X,∀ j ∈ X,c i.snd.fst=c j.snd.fst → ξ i=ξ j
omit [DecidableEq I] [Fintype I] in
-- using Set.Diff.Integer kept. Decidable for Census steps.
def font : Census (Unit× Recipe J V) where
   choices := Finset.univ.filter (fun i=>Clan c i)
   blank := mem_filter.mpr ⟨Finset.mem_univ _,fun i hi=> by simp at hi⟩
   solo k:= mem_filter.mpr ⟨Finset.mem_univ _,fun _ hi _ hj _=>congr_arg _ ((mem_singleton.mp hi).trans (mem_singleton.mp hj).symm)⟩
   down h _ hy:= mem_filter.mpr ⟨Finset.mem_univ _,fun _ hi _ hj he=> (show Clan c _ from (mem_filter.mp h).2) _ (hy hi) _ (hy hj) he⟩
-- pricing license to replenish to ANY subset
abbrev brisk (c:J→I):Census (Unit×Root J):= Lift (Stock.census I) (fun i => c i.snd.fst)
lemma pilot_paid : Pantry.Policy (basin J V) (font (J:=J) (V:=V) c) (brisk c):=by
    intro i; let t:= route (Pantry.all_le _ (brisk c)) i; let s:= i.val; let k:=fun j': L'=>c j'.snd.fst; have he: Lit (Stock.census I) k i.val:= (Finset.mem_filter.mp i.property).2
    change _ ∈ (Finset.univ.filter (fun i=>Clan c i))
    refine mem_filter.mpr ⟨Finset.mem_univ _,fun a ha b hb hp=> ?_⟩
    obtain ⟨j,hj,hP⟩:=mem_biUnion.mp ha; obtain ⟨j',hJ',hP'⟩:=mem_biUnion.mp hb
    rw [(Π).focuses] at hP hP'; apply (hP.trans (_ : j=j')).trans hP'.symm; apply he.2 hj hJ'; rw [← hP, ← hP']; exact hp

def turnL (J:Type): Unit × Root J≃ J×Bool:=Equiv.punitProd _
local notation "Γ"=> turnL J
lemma licensed : License (Lift (Stock.census I) c) (brisk c) (Prod.fst ∘ Γ):=by
    intro t h; have he: Lit (Stock.census I) (fun i: L' => c i.2.1) t:= (Lit.chain t).2 (show Lit (Lift (Stock.census I) c) (Prod.fst ∘ Γ) t from h); exact mem_filter.mpr ⟨Finset.mem_univ _,he⟩

abbrev back (J:Type)[Fintype J][DecidableEq J]:= Finset.univ.image (fun i:J=>(i,false))
omit [Fintype V] [DecidableEq V] in
lemma plain (i:T₁)(he:i∈back J) : (basin J V).Solo i:=by
    obtain ⟨j,hJ,rfl⟩:= mem_image.mp he; rintro ⟨j',(v|⟨⟩)⟩ h; exact False.elim (Bool.noConfusion (congr_arg Prod.snd h)); exact Prod.ext (congr_arg Prod.fst h).symm rfl
--      analysis
lemma basin_count (i:Unit×Root J) : (Π.contents i).card ≤ Fintype.card (Color V):=by
    let s:= (Π).contents i; let f:=fun x:L=>x.snd.snd
    exact (card_image_of_injOn (s:=s) (f:=f) (fun a ha b hb hv=> Prod.ext (Subsingleton.elim ..) (Prod.ext (congr_arg (fun i:L'=> i.snd.fst) (((Π).focuses ..).1 ha|>.trans (((Π).focuses ..).1 hb).symm)) hv))).symm.trans_le (Finset.card_le_univ _)

end Basket
end YM.RG05Readout.Records
