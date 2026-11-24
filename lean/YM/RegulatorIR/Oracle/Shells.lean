import YM.RegulatorIR.Oracle.Tune
import YM.Push.FREE_RESOLVENT.Masking

/-! Shell mask (here never a large-field mask). Orthogonal coordinate
projection removes the inactive tree directions exactly. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field Bark
open FreeResolvent (Slot PAC Vec component ix tensor)
open FreeResolvent.Shell
open Exterior RG Wilson Matrix Halo Profiles Push Precision
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G:Gauge}{n p: Side} {L:Side}{X:Type} {α σ:ℝ}(P:Patch)(H:KernelChoices)
-- note any n can be used.
def doormat (P:Patch)(x:Long G.ColorIndex):Prop:= around ((1:Side)*P.L) x.1 ∉ (stemF P 1).trunks

def renter (G:Gauge) (n:Side): FreeResolvent.Active G (stemF P n) ↪ FreeResolvent.Slot G (n*P.L) 1:= ⟨FreeResolvent.plant _,FreeResolvent.plant_inj _⟩

lemma admittedE (x:Long G.ColorIndex) : doormat P x ↔ around (n*P.L) x.1 ∉ (stemF P n).trunks:=not_congr (trunksW P x.1)
lemma permitsD (G:Gauge)(n:Side)(x:Long G.ColorIndex): (blockQ G P.L).swrap n x∈Set.range (renter P G n) ↔ doormat P x:=by
 rw [admittedE (n:=n) P,v_same, ← on_wrap]; constructor
 · rintro ⟨z,hz⟩ h
   change onslot G (n*P.L) (z.1.val,z.2)= _ at hz
   have ht: z.1.val=around _ x.1:= congr_arg Prod.fst ((onslot G (n*P.L)).injective hz); exact z.1.property (ht.symm ▸ h)
 intro h; exact ⟨(⟨around _ x.1,h⟩,x.2),rfl⟩
-- wraps to θ only with forest sign h
lemma turns_key (G:Gauge)(n:Side){P' l:ℝ}(he:Even (n*P.L).val)(hh:l*(n*P.L).val=P') : awake (avenue P H n) (stemF P n)∘(Carto G l P' he hh).orbit=doormat P:= by
 ext1 x; change (¬ Geometry.Field.branch (stemF P n) _) = _; simp_rw [admittedE (n:=n) P]; apply propext; exact not_congr (Geometry.Field.bone (F:=stemF P n) (Field.Square.proper _ P.odd_side) (around (n*P.L) x.1))

include H
lemma free_shift (G:Gauge)(x:Long G.ColorIndex)(d: Cover) : doormat P ((blockQ G P.L).shiftB d x)=doormat P x:=by
 let S:=avenue P H 1
 
 rw [strut]; have hp(v:Long G.ColorIndex):doormat P v= (¬ Field.branch (bios S) (Geometry.resolve ((1:Side)*P.L) v.1)):= propext (not_congr (bone (F:=stemF P 1) (Field.Square.proper _ P.odd_side) _)).symm
 rw [hp,hp]; exact congr_arg Not (Profiles.branch_path S d x.1)

def pension (G:Gauge):Layer (Long G.ColorIndex) (Long G.ColorIndex):=fun x y=> if x=y ∧ doormat P x then 1 else 0
lemma promised (G:Gauge) : Albedo (blockQ G P.L) (blockQ G P.L) (pension P G):=by
 intro i j d; unfold pension;simp_rw [(blockQ _ _|>.shiftB d).injective.eq_iff, free_shift P H G]
omit H
lemma pension_sym (G:Gauge): Function.swap (pension P G)=pension P G:=by ext1 x;ext1 y; unfold Function.swap pension; by_cases h:x=y <;> simp [h,eq_comm]
lemma pensionE (G:Gauge) : chestE (blockQ G P.L) (blockQ G P.L) σ (pension P G) 1 :=by
 refine fun i=>le_trans (quota_dom _ (ID _ i) (fun j=>?_)) (chestE.bright i); unfold pension ID; by_cases h:i=j <;> simp [h]; split <;> simp
lemma savings (G:Gauge): Billed (pension P G):= (pensionE (σ:=0) P G).billed le_rfl (by simp)
private lemma naught {I:Type}{f:I→ℝ}(h:∀ i,f i=0): (∑'i,f i)=0:=by simp_rw [h,tsum_zero]
include H
lemma physicalP (G:Gauge)(n:Side): ledgerRow (blockQ G P.L) (blockQ G P.L) (pension P G) n=rim (renter P G n):=by
 let D:= blockQ G P.L; ext1 i j; obtain ⟨x,hx⟩:=show ∃ x,D.swrap n x=i from ⟨_,D.both ..⟩
 rw [← hx]; rw [ledger_at D D _ (promised P H G),FreeResolvent.Shell.indicator]; simp only [D,permitsD]
 split
 next he=>
    obtain ⟨rfl,hx⟩:=he
    change (∑' y:Stalk (D.swrap n) (D.swrap n x), _)= _; rw [tsum_eq_single ⟨x,rfl⟩]
    · exact if_pos ⟨rfl,hx⟩
    intro i hi; exact if_neg (fun h=> hi (Subtype.ext h.1.symm))
 next he=> exact naught (fun i : Stalk (D.swrap n) j=>show pension P G x i.val=0 from if_neg (fun (h:x=i.val ∧ _) =>he ⟨h.1.symm ▸ i.property,h.2⟩)) -- lemma name

omit H
variable (G)
lemma albedo_mask (M:Layer (Long G.ColorIndex) X): lap (pension P G) M = clipL (doormat P) M:=by
 ext1 i;ext1 j; unfold clipL; split
 next h=> unfold lap; rw [tsum_eq_single i]; rw [pension,if_pos ⟨rfl,h⟩,one_mul]; intro y hy; unfold pension; rw [if_neg (fun h=>hy h.1.symm),zero_mul]
 next h=> unfold lap; apply naught; intro v; unfold pension; rw [if_neg (fun hp=>h hp.2),zero_mul]
lemma rent_eye (t:Patch) (g:Gauge) : lap (pension t g) (ID (Long g.ColorIndex))=pension t g:=by ext1 i;ext1 j;rw [albedo_mask]; unfold clipL ID pension; split_ifs <;> tauto
end YM.RegulatorIR.Oracle
