import YM.FormalBulk08.Bank.Dyad

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Bank
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Matrix Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa
open scoped Topology ENNReal BigOperators Classical ContDiff
variable {G : Gauge} {P : Patch} {K : KernelChoices} {n f : Side}
abbrev Rim (G : Gauge) (P : Patch) := Co P.L (Loc G 1)
abbrev Minor (G : Gauge) (P : Patch) (T : Lodge P):= Lodge.selected G P T
abbrev Board (G : Gauge) (P : Patch) := Rim G P ⊕ Loc G 1
abbrev BoardL (G : Gauge) (P : Patch) (T : Lodge P):= Minor G P T ⊕ Loc G 1

variable {S : StepData n f}
def staging (G : Gauge) (S : StepData n f) : Glob G n f ≃ Tor n (Board G S.patch):=(Equiv.sumCongr (splitCo S.ratio (Loc G 1)) (Equiv.refl _)).trans (bifid n _ _)
def saddleP (G : Gauge) (S : StepData n f) (T : Lodge S.patch) : Pine G S T.forest ⊕ wire G n≃ Tor n (BoardL G S.patch T) := (Equiv.sumCongr (T.splitting (G:=G)) (Equiv.refl _)).trans (bifid n _ _)

def pane (G : Gauge) (P : Patch) (T : Lodge P) := dye (transRows (touchRow T G)) 0 0 (unitRow (Loc G 1))
lemma pane_pay (T : Lodge P) (η : ℝ) : (pane G P T).strip η 1:= fileStrip (strip_trans (show (touchRow T G).strip η 1 from fun _ _=>Work.F08.strip_unit _ _)) (stillborn (by norm_num)) (stillborn (by norm_num)) (by apply Work.F08.strip_unit)

variable (S)
abbrev matPane (G:Gauge) (S:StepData n f) (T:Lodge S.patch):= Matrix.fromBlocks (dropRoot G S T.forest)ᵀ (0 : Matrix (wire G f) (wire G n) ℝ) 0 (1: Matrix (wire G n) (wire G n) ℝ)
lemma true_pane (T : Lodge S.patch) (v j) : (pane G S.patch T).acts n (staging G S v) (saddleP G S T j)= matPane G S T v j:= by
   refine Eq.trans (dye_spot (transRows (touchRow T G)) 0 0 (unitRow (Loc G 1)) n ((Equiv.sumCongr (unitSplit G S 1) (Equiv.refl (wire G n))) v) ((Equiv.sumCongr (T.splitting (S:=S)) (Equiv.refl (wire G n))) j)) ?_
   rw [acts_unit,deadActs,deadActs,acts_trans,touch_service S]; cases v <;> cases j <;> simp [matPane,repackM] <;> try rfl
   rename_i x y; change dropRoot _ _ _ ((T.splitting (S:=S)).symm ((T.splitting (S:=S)) y)) ((unitSplit G S 1).symm (unitSplit G S 1 x))= _; rw [(unitSplit G S 1).symm_apply_apply,(T.splitting (G:=G) (S:=S)).symm_apply_apply]
lemma paneG (T : Lodge S.patch) : graft (G:=G) (S:=S) T.forest = fun i=> matPane G S T *ᵥ i := by
   ext x a; cases a <;> simp [Matrix.fromBlocks_mulVec,matPane,graft, offer_as]

-- Composition of linear symbols
variable {V U : Type*}
lemma fixed_wires [Fintype V] [Fintype U] (A : Matrix V U ℝ) (F : Jets.Rays U→Jets.Rays V) (H : ContDiffAt ℝ ∞ F 0) (h : F=fun i=> A *ᵥ i) (i:V) : motor F i=C (mixRows A (MvPolynomial.X i)) := by
   apply photo; intro x
   have hf : ∀ (b : ℝ) a,F (b•a)=b•F a := fun b c=> by rw [h]; change A *ᵥ (b • c)= _; rw [mulVec_smul]
   have hh:=fixed_path x (fun v=>F v i) (coord_diff _ H i)
   have hg : glimpse x (paste (fun v=>F v i))=X^1*C (F x i) := unique_gaze hh (by simpa only [hf,pow_one,Pi.smul_apply,smul_eq_mul,pow_one] using gaze_leaf (F x i) 1)
   have hv : traceP x (mixRows A (MvPolynomial.X i))=F x i:=by simp [h,mixRows,traceP,Matrix.mulVec,dotProduct]
   rw [motor,after_move,hg,pow_one]; unfold glimpse; rw [PowerSeries.map_C]; ext1 k; rw [after_one,add_comm,coeff_succ_X_mul]; exact congr_arg (fun v=> coeff k (C v)) hv.symm
lemma pane_letter [Fintype V] [Fintype U] (A : Matrix V U ℝ) (F : Jets.Rays U→Jets.Rays V) (H : ContDiffAt ℝ ∞ F 0) (h : F=fun i=> A*ᵥ i) (p : Pap V) : roam ℝ (motor F) p= PowerSeries.map (mixRows A).toRingHom p := by
   unfold roam;rw [show insertAt ℝ _ = C.comp _ from ?he,pure_map]
   case he=> ext <;> simp [fixed_wires A F H h]
lemma mix_pane {V X U Y : Type*} [Fintype U] [Fintype Y] (L : V→U→ℝ) (M : X→Y→ℝ) (e : V≃X) (g : U≃Y) (h : ∀ i j,M (e i) (g j)=L i j) (p : Pap V):
    joust g (PowerSeries.map (mixRows L).toRingHom p)=PowerSeries.map (mixRows M).toRingHom (joust e p) := by
   unfold joust; rw [←RingHom.comp_apply,←RingHom.comp_apply (PowerSeries.map (mixRows M).toRingHom),← PowerSeries.map_comp,←PowerSeries.map_comp]
   have he : (MvPolynomial.rename g).toRingHom.comp (mixRows L).toRingHom = (mixRows M).toRingHom.comp (MvPolynomial.rename e).toRingHom := by
       ext
       case hC _ _=> simp
       case hX i k=>
           have he: MvPolynomial.rename g (mixRows L (MvPolynomial.X i))=mixRows M (MvPolynomial.X (e i)):=by simp [mixRows]; exact Fintype.sum_equiv g _ _ fun j=>by rw [h]
           apply congr_arg (MvPolynomial.coeff k);simpa using he
   rw [he]
lemma becoming (T:Lodge S.patch) (p: Pap (Glob G n f)): joust (saddleP G S T) (roam ℝ (motor (graft T.forest)) p)=PowerSeries.map (mixRows ((pane G S.patch T).acts n)).toRingHom (joust (staging G S) p) := by
   rw [pane_letter _ _ ((graft_receipt (S:=S) (G:=G) T.forest).of_le le_top) (paneG S T) p]; apply mix_pane; exact true_pane S T
end YM.FormalBulk08.Bank
