import YM.FormalOPE.RG10.Routes.Channel
import YM.FormalOPE.RG10.Routes.LogWeight

/-!
# Concrete functional formula for a binary joining discrepancy, any order

An exposed PS with normalization (full products, consistent repeated rank, tree-gauge/no tags
options where supplied). Inputs can be full polynomial bundles previously obtained by multi-step
transfer; no assumption independences or a trace normalization. In particular a producer may
combine **smeared** packs of sources before transferring from top to any joint scale; their
ordinary multipoint correlations telescope with exactly the estimates on this binary paid
amount, not an artificial multiplication of independently conditioned factors. Note the polar
factorial repacking of every identified vertex and the canonical width `posted`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Route.Binary
open Marker Extra.Trajectories FlatFeed Word Polar PowerSeries Finset Joins Joins.Gauss Function
open MvPolynomial (aeval coeff_sum)
open Multi (parts shards)
open Multi.Vacuum.Gauss (Row)
open scoped BigOperators Topology Classical
variable {I J B K : Type} [Fintype J] [Fintype K] [DecidableEq K]
    (q : I→Row J) (P Q V : Channel (I⊕ B))
abbrev bill := PolyUtil.freely Bool

local notation "T" => Polar.budget bill K
def bothMarks : bill.Mode := ⟨{false,true},mem_univ _⟩
lemma marks4 (s : bill.Mode) : s=bill.quiet ∨ s=bill.fire false ∨ s=bill.fire true ∨ s=bothMarks := by
  by_cases he : false ∈ s.val <;> by_cases h : true ∈ s.val
  · right; right; right; apply Subtype.ext; ext i; cases i <;> simp [bothMarks,h,he]
  · right; left; apply Subtype.ext; ext i; cases i <;> simp [Census.fire,h,he]
  · right; right; left; apply Subtype.ext; ext i; cases i <;> simp [Census.fire,h,he]
  left; apply Subtype.ext; ext i; cases i <;> simp [Census.quiet,h,he]
@[simp] lemma both_ne_quiet : bothMarks ≠ bill.quiet := by intro h; simpa [bothMarks,Census.quiet] using congr_arg Subtype.val h
@[simp] lemma both_ne_fire (v : Bool) : bothMarks ≠ bill.fire v := by intro h; cases v <;> simpa [bothMarks,Census.fire] using congr_arg Finset.card (congr_arg Subtype.val h)
@[simp] lemma marker_ne_quiet (v : Bool) : bill.fire v ≠ bill.quiet := by intro h; simpa [Census.fire,Census.quiet] using congr_arg Subtype.val h

abbrev Target (K : Type) [Fintype K] [DecidableEq K] := Payload K bill

def selectGen (v : bill.Mode) := if v= bill.quiet then V else if v=bill.fire false then P else if v=bill.fire true then Q else 0
def posted (p : Target K) := (↑(Polar.tickets p.val).card.factorial:ℂ) • coeff (Polar.tickets p.val).card (selectGen P Q V (Polar.mark p.val))
local notation "F" => standardFeed J
local notation "δ" => posted P Q V

variable (y : B→ℂ) (hz : PowerSeries.coeff 0 V=0)
local notation "W" => Bulk.intake q y V hz

def contribution (v : Bool) : Kernel (Unit × Row J) := if v=false then Bulk.water q y P else Bulk.water q y Q
def speak (y : B→ℂ) (x:Unit× Row J) := emit bill (fun a => contribution q P Q y a x)

private lemma vocal : Word.read bill.quiet (speak q P Q y)=1 := funext fun x => Word.emit_unit (R:=bill) (fun a=>contribution q P Q y a x)

include hz
private lemma price (x) (a : bill.Mode) : see a (logWord (totalize W (speak q P Q y) x)) = Bulk.water q y (selectGen P Q V a) x := by
  let C := Bulk.water q y V
  let B := speak q P Q y x
  have he : totalize W (speak q P Q y) x = Ex bill (expTaylor (C x)) * B := by
    unfold totalize; simp_rw [Bulk.heaviness]; rw [show (Bulk.water q y (advance V)) x=expTaylor (C x) from advanced V (Sum.elim (alongFine q x.2) y)]; rfl
  rw [he,log_mul,log_weight]; swap
  · exact congr_fun (W).V0 x
  rotate_left
  · rw [boot,vac_eq,plain, if_pos rfl]; simp [expTaylor]
  · unfold B boot; rw [vac_eq]; change coeff 0 (Word.read _ _ _)=_; rw [vocal]; exact PowerSeries.coeff_zero_one -- inspect
  have hx : vac bill B=1:= Word.emit_unit _
  have hf : see (bill.fire false) B = Bulk.water q y P x := by unfold B speak; rw [emit_part]; simp [Census.fire, contribution]
  have hb : see (bill.fire true) B = Bulk.water q y Q x := by unfold B speak; rw [emit_part]; simp [Census.fire, contribution]
  rw [see_add, plain]; unfold selectGen
  obtain rfl|h|h|h:= marks4 a
  · -- will handle case s=bill.quiet
    rw [← vac_eq,vac_log _ hx]; simp; rfl
  · subst a; rw [alone B hx, hf]; simp
  · subst a; rw [alone B hx, hb]; simp
  subst a; rw [crown B hx bothMarks (show false ≠ true by decide) rfl, hf,hb]
  unfold B speak; simp only [emit_part, both_ne_fire, both_ne_quiet, ite_false]; simp [contribution,bothMarks]

private lemma performs : Parsed q (fun y=> Bulk.intake q y V hz) (speak q P Q) (posted (K:=K) P Q V) := by
  intro y; have hu := performs_canonical (I:=K) (Bulk.intake q y V hz) (speak q P Q y) (vocal q P Q y)
  refine (show driver (Bulk.intake q y V hz) K (speak q P Q y)=(fun v=>(study q y (δ (show Target K from v))).val) from ?_) ▸ hu
  funext v x
  unfold driver
  have h : boot (totalize (Bulk.intake q y V hz) (speak q P Q y) x)=1:= weight_and_input _ _ (vocal q P Q y) _
  rw [← certify_present,← consistent _ h, certify_present]; unfold present
  change (↑(tickets v.val).card.factorial:ℂ) * (coeff (R:=Poly bill) (tickets v.val).card _).part (mark v.val) = _
  rw [← unfold_see,price]; unfold posted; rw [map_smul]; congr; exact Bulk.watered q y (selectGen P Q V (mark v.val)) x (tickets v.val).card -- inspect

def disagreement := Bulk.transfer q (P*Q) V- Bulk.transfer q P V * Bulk.transfer q Q V

lemma speaks : run y (disagreement q P Q V)=
      see bothMarks ((F).contraction W (speak q P Q y)) := by
  rw [disagreement,map_sub,map_mul]; unfold speak; rw [contract_pair _ _ _ rfl (show false≠true by decide)];
  simp only [pairConnected,Bulk.unfolds_step q y _ V hz,contribution,ite_true,Bool.true_eq_false,ite_false,map_mul]

theorem resolution (k : Finset K) : (↑k.card.factorial:ℂ) • coeff k.card (disagreement q P Q V) =
    ∑ i∈shards T (Polar.pay bothMarks k), track q i (posted P Q V) := by
  apply all_conf; intro y; rw [map_smul,← run_charge,speaks q P Q V y hz];
  exact (locate q _ _ δ y (performs q P Q V hz) _ ⟨false,Finset.mem_insert_self ..⟩ (vocal q P Q y) k).symm
end YM.FormalOPE.RG10.Route.Binary
