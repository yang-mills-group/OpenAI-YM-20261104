import YM.RegulatorIR.Oracle.Ice

/-! Pack quadratic schemes over actual finite parameters. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field Bark
open FreeResolvent (Slot PAC Vec component ix tensor)
open Exterior RG Wilson Matrix Halo Profiles Push Precision
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G:Gauge}{n p:Side}{X Y:Type}

variable (P:Patch)(K:KernelChoices)(G:Gauge)(B D:Bed)(R:Cross P.L (TypeFace 1) (TypeFace 1))
local notation "A0"=> projectionQ P K R G
local notation "Q"=> OrthoQ P K G
local notation "Kg"=> stableK P K G B
local notation "A"=> blockQ G P.L
local notation "T"=> linksQ G
local notation "L"=> pension P G
variable {σ τ Ω Ω' α α' υ m:ℝ} {S S':Clip}
variable (F:Hall B σ Ω α S)(C:Hall D τ Ω' α' S')(Z:P.Branches K G)
variable (H:BidP P K B D R σ υ)(Xv:∀ n,Bid.Sworn B n G)
include F C H Z Xv
lemma restoring : Flurry A0=A0:=by
 let C':= cousin P K G B; let B':=cable P K G B F Z; let Z':= lap L (K.penalty • Function.swap Q)
 have hp:=((overrides P K R G H.rows F.pos.le H.costV).buys F.pos.le).1;have hQ:=effects P K G B F Z|>.choose_spec
 have hc:Billed C':=(shellsC P K G B F).billed F.pos.le (by unfold trunkCost; finiteness)
 have he: Flurry Z'=Z':=by unfold Z'; rw [← Flurry.board,pension_ice,Flurry.power]; rw [show Flurry (Function.swap Q)=_ from congr_arg (fun z: Layer _ _ => Function.swap z) (snowed_K G P K Z)]
 have ht: lap B' Z'= A0 :=by unfold Z'; rw [← aspect P K G B D R F C H]; rw [medallion A T (cafe P K G B F Z) hc hp hQ.1 (spliceR P K G B) (placates P K R G), show lap B' C'= ID _ from hQ.2.2.2, lefte]
 rw [← ht, ← Flurry.board, cable_ice P K G B F Z Xv,he]

omit F C H Z Xv
lemma gears_A {r s:ℝ} (he:Even n.val)(hc:r*n.val=s){F:Layer (Long G.ColorIndex) (Long G.ColorIndex)} (h:Albedo (linksQ G) (linksQ G) F)(hz:Flurry F=F) : Sym (Carto G r s he hc) (Carto G r s he hc) F :=by
 rintro (d|d) x y
 · change F (motionsQ x (n.val • d)) (motionsQ y (n.val • d))= _;rw [← site_roll,← site_roll]; exact h ..
 let TQ:=snow G; let v:n.val= n.val:=rfl
 change F (motionsQ (TQ x) (n.val • d)) (motionsQ (TQ y) (n.val • d))=_; rw [← site_roll,← site_roll,h]; exact congr_fun (congr_fun hz x) y
lemma gears_B {r s:ℝ} (he:Even (n*P.L).val)(hc:r*(n*P.L).val=s){F:Layer (Long G.ColorIndex) (Long G.ColorIndex)} (h:Albedo A A F)(hz:Flurry F=F): Sym (Carto G r s he hc) (Carto G r s he hc) F :=by
 have hv(d:Cover):(n*P.L).val • d=P.L.val • n.val • d:=by rw [smul_smul,Nat.mul_comm P.L.val];rfl
 rintro (d|d) x y
 · change F (motionsQ x _) (motionsQ y _)= _;rw [hv,← strut,← strut]; exact h ..
 let G':=snow G; change F (motionsQ (G' x) ((n*P.L).val • d)) (motionsQ (G' y) _)=_;rw [hv,← strut,← strut,h]; exact congr_fun (congr_fun hz x) y
lemma gears_C{r s l:ℝ} (he:Even (n*P.L).val)(hc:r*(n*P.L).val=s)(hn:Even n.val)(ht:l*n.val=s){F:Layer (Long G.ColorIndex) (Long G.ColorIndex)} (h:Albedo A T F)(hz:Flurry F=F): Sym (Carto G r s he hc) (Carto G l s hn ht) F:=by
 have hv(d:Cover):(n*P.L).val • d=P.L.val • n.val • d:=by rw [smul_smul,Nat.mul_comm P.L.val];rfl
 rintro (d|d) x y
 · change F (motionsQ x _) (motionsQ y _)= _;rw [hv,← strut,← site_roll]; exact h ..
 let G':=snow G; change F (motionsQ (G' x) ((n*P.L).val • d)) (motionsQ (G' y) _)=_;rw [hv,← strut,← site_roll,h]; exact congr_fun (congr_fun hz x) y
include F C H Z Xv
set_option maxHeartbeats 380000 in
lemma worth_E {r s l:ℝ} (he:Even (n*P.L).val)(hc:r*(n*P.L).val=s)(hn:Even n.val)(ht:l*n.val=s) : Bedload (Carto G r s he hc) (Carto G l s hn ht) K.penalty (awake (avenue P K n) (stemF P n)) (crust G B) (crust G D) (finer (fringe (avenue P K n))) A0 (hearth P K G B F Z):=by
 rw [← Rubric];
 have hs :Sym (Carto G r s he hc) (Carto G l s hn ht) (Function.swap Q):= gears_C P G he hc hn ht (stampD P K G|>.swap) (congr_arg (fun f:Layer (Long G.ColorIndex) (Long G.ColorIndex)=> Function.swap f) (snowed_K G P K Z))
 let P':= awake (avenue P K n) (stemF P n) (G:=G)
 let N:= Carto G r s he hc
 let U:= hearth P K G B F Z
 obtain ⟨z,h₁⟩:= (priced_D P K G σ).buys F.pos.le
 have hy:P' ∘ N.orbit=doormat P:=turns_key P K G n he hc
 have hv : lap L A0=A0:= ministry P K G B D R F H
 obtain ⟨ha,hq⟩:= crown P K G B F Z
 obtain ⟨a,b⟩:= marches P K G B D R F C H
 rw [albedo_mask] at ha hq hv
 exact {
  rows:=⟨crust_f G B F.stripP.2.1 F.pos.le F.paid,z,h₁, ((overrides P K R G H.rows F.pos.le H.costV).buys F.pos.le).1,heatP P K G B F Z ⟩
  sym:=⟨gears_A G he hc (crustA G B) (tune_s G B F Xv), fun d x y=>hs d y x, gears_C P G he hc hn ht (placates P K R G) (restoring P K G B D R F C Z H Xv), gears_B P G he hc (phaseT P K G B F Z) (thaws P K G B F Z Xv)⟩
  symmetric:=symmetry_h G B F.floorP F.pos.le F.paid F.stripP.2.1
  mean:=fun i j hi=>Eq.symm (congr_fun (congr_fun hv i) j)|>.trans (if_neg ((congr_fun hy i) ▸ hi)), inverse:=fun i j hi=>Eq.symm (congr_fun (congr_fun hq i) j)|>.trans (if_neg ((congr_fun hy i) ▸ hi))
  sheet:= congr_arg (clipL (P'∘ N.orbit)) a
  feather:=by rw [hy]; exact ha.trans ((rent_eye P G).symm.trans (albedo_mask G P _))
  energy:=b }
end YM.RegulatorIR.Oracle
