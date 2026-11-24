import YM.Frontier6.Multi.Storage.Passage
/-! Panel conversion from advancing slots for arbitrary subset of leaders.
Local assumption on occupancy charges even **on** coincidence of the
projected native-grid locations; aan matched center occupancy finalized elsewhere.
No projection suppressed on the leg. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Canopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V C O:Type}[Fintype V][DecidableEq V][Fintype O][DecidableEq O][Fintype C][DecidableEq C]
variable {G:Gauge}
section
variable {H:History G}{δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p i,i<N→GaugeDoor (H.rep N p (i+1)) (H.rep N p i)}
variable {N p i:ℕ}{σ χ:ℕ→ℝ}(v:V) (P:V→Motion)(B:V→Equiv.Perm V)
   (E:∀ i:ℕ,V→Site (H.S.side i p))(o:∀ i:ℕ,Live V O→Site (H.S.side i p))
set_option quotPrecheck false
local notation "P'"=> H.levels.budget
local notation "R"=> H.rep N p
local notation "X"=> (Now V O)
variable (h:H.Selected)(μ:ℕ)(hr:Thor H δ r D σ χ μ) (w:O→ℝ)
    (F:Config G (H.S.side i p)→Poly (Now V O)) (hF:Atlas H v P B E o δ χ i (N:=N) F w) (hw:∀ i,0<w i)
include h hr hF hw
def inscribed (A: Levels G)(i:ℕ):= 4*(A.budget i).B^2+1
def pence (A:Levels G)(i:ℕ)(δ:ℕ→ℝ)(w:O→ℝ):O→ℝ:= Salt.tow w ((A.budget i).supportExponent+1/2) (δ i) (inscribed A i)
def lot (A:Levels G)(i:ℕ)(δ:ℕ→ℝ)(π:Concentrate O C)(w:O→ℝ)(j:C):ℝ:=∏ b∈π.fiber j,pence A i δ w b
local notation "c!"=>Salt.scent (P' i).B (r i) ((P' i).supportExponent+1/2) 1 (δ i) 1 (χ i)
local notation "w!"=> (lot H.levels i δ)
local notation "J"=> (P' i).B
omit h hr hF hw in
lemma Anchorage {A:Levels G}(i:ℕ)(δ:ℕ→ℝ)(w:O→ℝ)(π:Concentrate O C) (he:0< δ i)(hu:∀ j,0<w j)(b:C):0 < lot A i δ π w b:= prod_pos (fun j _=> Salt.towP _ _ _ _ hu he j) -- omit
lemma congregate (π:Concentrate O C)(hp:μ < i)(hN:i<N)(hs:Shaped v P (E i) (o i))(hy:Between (o i) ((P' i).B)) (hO:Fintype.card O ≤ r i)(hd:∀ b:O,separation (o i (v,b)) (o i (v,π.seat (π.hit b))) ≤ (H.levels.budget i).B^2)
    (hB:∀ j,j≠v→ B j v=j) (hV: (((H.levels.budget i).B+(H.levels.budget i).B+1:ℕ):ℝ)^4 * c! ≤ 1/2)(hC: Real.exp (c!)-1 ≤ 1) :
    let w':= lot H.levels i δ π w
    Parcels H v P B E (fun i=>o i ∘ (batt π).seat) i (N:=N) ((batt π).reap ∘ F) (fun j=>w' j/8) 0:=by
    intro w'; have hk:= (h.represents N p i hN.le); have he:= (hr.suns i hp.le).hats; obtain ⟨F',L,u,hZ,hX,hK⟩:= hF.sells; have hv:= hk.vac
    have hA: Arsenal (R i):= by
       cases i with
       | zero=> omega
       | succ i=> exact (hr.moon N p i (by omega) (by omega)).1.contact
    let o':= o i ∘ (batt π).seat; have hw'(j):0 < w' j:= prod_pos (fun j _=> Salt.towP _ _ _ _ hw he.1 j)
    have hf(j:Live V O): coverNumber (J) ({o i j, o' ((batt π).hit j)}:Support _) ≤ inscribed H.levels i:=by
       apply (Frontier6.pair_cover _ _ (P' i).B_pos).trans; apply Nat.add_le_add_right (Nat.mul_le_mul_left 4 _) 1; rcases j with ⟨x,j⟩
       change separation (o i (x,j)) (o i (x,_)) ≤ _; rw [hs.right v (o i)]; exact hd j
    obtain ⟨g,k,hY,hL,hM⟩:= grafted π (r i) (inscribed H.levels i) (δ i) 1 1 hA (hv.symm ▸ hZ) hk.good.labels (fun x hx=> ⟨hB x hx,fun j=>⟨hs x hx j,hK x hx j⟩⟩) (fun j=>hw j.2) (hy.sectors _ _ (r i) hO (P' i|>.B_pos)) (hy.compacted _ _ _ (by assumption) (P' i|>.B_pos) π) (zero_le_one) hX (by rw [hv]; exact (P' i).B_pos) he.1 he.2 (by rw [hv]; exact hf) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num) (fun U=>(Tour.bright H h N p i hN.le U).ne') (w:=(fun j=> w' j.2)) (fun j=>by rw [hv]; exact (team π (pence H.levels i δ w) j.1 j.2).symm) (hv.symm ▸ hV) (hv.symm ▸ hC)
    have he'(j):0 < w' j/8:= div_pos (hw' j) (by norm_num)
    rw [hv] at hY
    refine ⟨g,k,hY.prune (fun j=>hw' j.2) (fun j=> he' j.2) (slighter (fun j=>hw' j.2) (fun j=> he' j.2) (w:=1) (fun j=>?_ ) zero_le_one le_rfl) zero_le_one (by simp) (by norm_num),hM,fun j=>(hL j).1,fun j=>?_⟩
    · rw [one_mul]; exact div_le_self (hw' _|>.le) (by norm_num)
    · apply (hL (v,j)).2.more; change 4*(1/w' j) ≤ 1/(2*(w' j/8)); apply le_of_eq; have ht := hw' j; field_simp; ring

lemma activation (hA: Arsenal (H.rep N p i)) (hk:i ≤ N)(he:χ i≤1)(hp:μ ≤ i): Stores H v P B E o i (N:=N) F (fun j=>w j/8):=by
   have hk:= h.represents N p i hk; obtain ⟨g,k,l,hZ,hU,hM⟩:= hF.sells
   have ht(j): w j/8 ≤ w j:= div_le_self (hw j|>.le) (by norm_num)
   have he' j:0< w j/8:= div_pos (hw j) (by norm_num)
   obtain ⟨f,L,hv,hd,hS⟩:= stem hA (hk.vac.symm ▸ hZ) hk.good.labels hM (fun i=> hw i.2) he (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1) (fun U=>(Tour.bright H h N p i (by assumption) U).ne')
   rw [hk.vac] at hS; refine ⟨he',l, ⟨f,L,hS.prune (fun i=> hw i.2) (fun j=>he' j.2) (slighter (fun j=> hw j.2) (fun j=> he' j.2) (w:=1) (fun j=>by rw [one_mul]; exact ht j.2) zero_le_one le_rfl) zero_le_one (by simp) (by norm_num),hd, fun j=> (hv j).1,fun j=>?_⟩,fun j=> (mul_le_mul_of_nonneg_right (ht j.2) (norm_nonneg _)).trans (hU j)⟩
   apply (hv (v,j)).2.more; calc
     _ ≤ 2*(1/w j)+2*(1/w j):= add_le_add le_rfl (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right he (hw j|>.le)) zero_le_two)
     _ = _ := by have hz:=hw j; field_simp; ring
end
end YM.MergeProof.Canopies
