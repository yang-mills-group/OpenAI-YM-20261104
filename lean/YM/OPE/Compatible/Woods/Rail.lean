import YM.OPE.Compatible.Woods.Steam
/-!
# True period reads of virtual trees and free conditional mean (absolute).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Woody
open Function Filter Set Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Next.Free FreeResolvent
open scoped Topology BigOperators ComplexConjugate
variable {G: Gauge}{ι:Type*}{c f L:Side}{j: ℕ}{P:Patch}{C:KernelChoices}{η A s: ℝ}
local notation "T" => TypeFace 1
lemma tensor_scale (A:Matrix (Body 1 f) (Body 1 c) ℝ) (v:ℝ) : tensor G (v • A)=v • tensor G A:= by ext ⟨x,b,i⟩ ⟨y,d,j⟩; cases Classical.em (i=j) <;> rename_i he <;> simp [he, tensor]
def scriptQ (G:Gauge)(P:Patch)(C:KernelChoices): Cross P.L (PAC G 1) (PAC G 1):= scaleRows C.penalty (forestWalk G (transRows (probeRow P)))
lemma scriptQ_read (G:Gauge)(S : StepData c f): installed S.ratio (scriptQ G S.patch S.kernel)=tensor G (S.kernel.penalty • (probe S).transpose):=by
   have he : installed S.ratio (transRows (probeRow S.patch)) = (probe S).transpose:=by rw [installed,acts_trans,block_probe];rfl
   rw [tensor_scale]; change ((scaleRows S.kernel.penalty _).acts c).submatrix _ _ = _; erw [acts_scale]; change S.kernel.penalty • (installed S.ratio (forestWalk G _)) = _; erw [forestWalk_read,he]
lemma scriptQ_pay (G:Gauge)(P:Patch)(C:KernelChoices):Whole (scriptQ G P C) :=by
   obtain ⟨M,h,hM⟩:=probe_ready P 1 zero_le_one; exact ⟨1,_,one_pos,strip_scale (forestWalk_pay (strip_trans hM) h) _⟩
namespace Medal
open Frequency
variable {S: StepData c f} (hp:Odd S.patch.L.val)
-- define active and cross installed
local notation "L" => forest S.ratio hp
local notation "Y" => plant (G:=G) L
local notation "U" => squad S.ratio hp G
def line (P:Patch)(C:KernelChoices)(G:Gauge): Row (Slip G P.L) (PAC G 1):= net  (into G _) (scriptQ G P C)
lemma line_read : reduce G S L * tensor G (S.kernel.penalty • (probe S)ᵀ)= ((line S.patch S.kernel G).acts c).submatrix U id:=by
     rw [← scriptQ_read, reduce, into_trunks, transpose_submatrix]
     let N := installed S.ratio (scriptQ G S.patch S.kernel)
     let u:= installed S.ratio (into G S.ratio.count)
     have hg: (line S.patch S.kernel G).acts c = u.transpose * N := net_action S.ratio (into_good G _) (scriptQ_pay G _ _)
     erw [hg]; rfl
lemma line_p (P:Patch)(C:KernelChoices)(G:Gauge): Whole (line P C G):=(into_good G _).flipped.prod (scriptQ_pay G _ _)
variable (B: Medal P G C j)(D: Train j)
def rowNet : Row (Slip G P.L) (PAC G 1):= composeRows (B.V D) (line P C G)
def highCross : Cross P.L (PAC G 1) (PAC G 1):= composeRows (into G P.L) (B.rowNet D)
lemma row_p : Whole (B.rowNet D):=(B.whole D).prod (line_p ..)
lemma high_p : Whole (B.highCross D) := (into_good ..).prod (B.row_p D)
lemma rolled (C : Medal S.patch G S.kernel j) (h:4≤j): installed S.ratio (C.highCross D)= FreeResolvent.covariance G S L (pink S.kernel.penalty D)*tensor G (S.kernel.penalty • (probe S)ᵀ):=by
     rw [FreeResolvent.covariance]; erw [C.measure_pond S hp _ h, Matrix.mul_assoc, Matrix.mul_assoc,line_read hp]
     rw [into_trunks]; erw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
     have hv := Whole.from_coarse S.ratio (into_good G _) (C.row_p D); unfold highCross; erw [hv]; unfold rowNet; erw [(C.whole D).acts (line_p _ _ G)]; try rfl
end Medal
end YM.OPE.Woody
