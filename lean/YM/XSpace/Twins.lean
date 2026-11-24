import YM.XSpace.Compat.LowSector
import YM.XSpace.DeepBond
import YangMills.WilsonProof.NativeSupport.YM.Next.MAXWELL.Canopy
/-!
# Skew turned fields at horizon 4. A purely signed-permutation proof.

Parity across four axes decomposes the quadratic labels into squares, common-edge-point
pairs, and complementary edges. In each parity class can swap any two of those monomials by
an order-two coordinate permutation -- even when there's one curvature on the other pair's
axes (tilt sign multiplies to `+`). Below a small exhaustive proof for that 4-axis fact.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Filter Set Maxwell Maxwell.Free Maxwell.Wick
open scoped Topology ContDiff BigOperators
variable {G : Gauge}

abbrev Index := Fin 6
section table
def left : Index → Axis := ![0,0,0,1,1,2]
def right : Index → Axis := ![1,2,3,2,3,3]
lemma cover_pairs (a b : Axis) (h : a < b) : ∃ i : Index,left i=a ∧ right i=b := (show ∀ a b:Axis,a<b→ ∃ i : Index,left i=a ∧ right i=b from by decide) a b h

-- flip parity for mirror a
def picked (i : Index) (a : Axis) : Bool := decide (a=left i ∨ a=right i)
def mark (i j : Index) (a : Axis) : Bool := !(picked i a == picked j a)
def twin (F : Axis → Axis) (i j : Index) := (F (left i)=left j ∧ F (right i)= right j) ∨ (F (left i)=right j ∧ F (right i)= left j)
instance (F : Axis→Axis) (i j:Index) : Decidable (twin F i j) := by unfold twin; infer_instance
-- possible involutions on coordinates used here
def table : Fin 10 → Axis → Axis := ![
 ![0,1,2,3],
 ![1,0,2,3],![2,1,0,3],![3,1,2,0],![0,2,1,3],![0,3,2,1],![0,1,3,2],
 ![1,0,3,2],![2,3,0,1],![3,2,1,0]]
lemma twin_table (a : Fin 10) (p : Axis): table a (table a p)=p:= (by decide : ∀ a p, table a (table a p)=p) a p
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
lemma twin_check : ∀ i j k l, i≤j → k≤l → (∃ a, mark i j a ≠ mark k l a) ∨
    ∃ b : Fin 10, twin (table b) i k ∧ twin (table b) j l ∨ twin (table b) i l ∧ twin (table b) j k := by
  decide
end table
variable {T : Module.End ℂ (WickPol G)} {d : ℕ}

def label (G : Gauge) (i j : Index) := team G (cell (left i) (right i)) (cell (left j) (right j))
lemma turn_cell (a : Axis) (i : Index): actFlavor (Signed.mirror a).ortho 0 (cell (left i) (right i))=
    if picked i a then -cell (left i) (right i) else cell (left i) (right i):= by
  rw [tilt_one]
  have he:= (by decide : ∀ i,left i≠right i) i
  by_cases ha : a=left i <;> by_cases hb : a=right i <;> simp_all [tilt,Signed.mirror,picked,Ne.symm] <;> exact neg_one_smul ℝ (cell (left i) (right i))
lemma turn_label (a : Axis) (i j : Index): reflectPol (Signed.mirror a).ortho (label G i j) =
    if mark i j a then -label G i j else label G i j:= by
  unfold label; rw [orient_team, turn_cell a,turn_cell a]
  let X := duetL G 0 0
  simp_rw [show ∀ p q : Flavor 0, team G p q=X p q from fun _ _=> rfl]; cases h : picked i a <;> cases he : picked j a <;> simp [mark,h,he]
lemma label_span : Teams G 0 0= Submodule.span ℂ {p | ∃ i j : Index,i≤j ∧ p=label G i j}:=by
  let J := Submodule.span ℂ {p| ∃ i j : Index, i≤j ∧ p=label G i j}
  apply le_antisymm
  · have hh (a b : Index) : label G a b∈ J:=by
      apply Submodule.subset_span
      rcases le_total a b with h|h; exact ⟨_,_,h,rfl⟩
      exact ⟨_,_,h,team_swap G _ _⟩
    have he : Submodule.span ℝ (range fun i : Index=> cell (left i) (right i))=⊤:= by
      refine eq_top_iff.mpr ?_
      rw [← cell_span]; apply Submodule.span_mono; rintro u ⟨a,b,h,rfl⟩; obtain ⟨i,rfl,rfl⟩:=cover_pairs a b h; exact ⟨i,rfl⟩
    rw [Teams,Submodule.span_le]; rintro p ⟨p,q,rfl⟩
    have hi i (p : Flavor 0) : team G (cell (left i) (right i)) p∈ J := by
      let b := (duetL G 0 0 (cell (left i) (right i)))
      change p∈ (J.restrictScalars ℝ).comap b
      apply (show ⊤ ≤ (J.restrictScalars ℝ).comap b from ?_) (Submodule.mem_top)
      rw [← he, Submodule.span_le]; rintro v ⟨j,rfl⟩; exact hh i j
    have ht : ⊤ ≤ (J.restrictScalars ℝ).comap (duetL G 0 0 q):=by
      rw [← he,Submodule.span_le]; rintro v ⟨j,rfl⟩; change team G _ _∈ J; rw [team_swap]; exact hi j q
    change team G p q∈J; rw [team_swap]; exact ht (Submodule.mem_top)
  rw [Submodule.span_le]; rintro x ⟨i,j,-,rfl⟩; exact in_team G _ _

def tperm (b : Fin 10) : Signed := ⟨⟨table b,table b,twin_table b,twin_table b⟩, fun _=> false⟩
lemma tperm_inv (b : Fin 10) : (tperm b)⁻¹ = tperm b := rfl
lemma label_twin (b i j k l) (hh : twin (table b) i k) (ht : twin (table b) j l):
    reflectPol (tperm b).ortho (label G i j)=label G k l ∨ reflectPol (tperm b).ortho (label G i j) = -label G k l:= by
  unfold label; rw [orient_team]
  have he (i j) (h:twin (table b) i j) : actFlavor (tperm b).ortho 0 (cell (left i) (right i))=cell (left j) (right j) ∨ actFlavor (tperm b).ortho 0 (cell (left i) (right i))= -cell (left j) (right j):=by
    rcases h with h|h <;> simp [tilt_one,tilt,tperm,h,cell_skew (right j) (left j)]
  simp_rw [show ∀ (p q : Flavor 0), team G p q=duetL G 0 0 p q from fun _ _=>rfl]
  rcases he _ _ hh with ha|ha <;> rcases he _ _ ht with hb|hb <;> simp [ha,hb]

lemma flick (i j k l : Index) (hl : i≤j) (hv : k≤l) (h : G.Simple) (H : Equivariant d T) (hy : silence G d T)
    (hd : 4≤d) (hi : T (label G i j) ∈ shellSector G 4) : Slot T (label G i j) (label G k l)=0:=by
  let a := label G i j; let b:=label G k l
  have ha : a∈shellSector G 4:=team_label _ _ le_rfl
  have hb : b∈shellSector G 4:=team_label _ _ le_rfl
  have hn {x : ℂ} (hm : x+x=0): x=0:= (mul_eq_zero.mp (show 2*x=0 from (two_mul x).trans hm)).resolve_left (by norm_num)
  rcases twin_check i j k l hl hv with ⟨r,hr⟩|⟨r,hr⟩
  · have hh:=same_slot (Signed.mirror r) h hd H hi ha hb
    simp_rw [b] at hh; rw [turn_label,turn_label] at hh
    suffices -(Slot T (label G i j) (label G k l))=Slot T (label G i j) (label G k l) by apply hn; nth_rw 1 [← this]; abel
    cases h₁ : mark i j r <;> cases h₂ : mark k l r <;> simp_all
  let t:=(tperm r).ortho
  have he : reflectPol t (reflectPol t a)=a:=by
    rw [← pol_mul,show t*t=1 by nth_rw 1 [show t=t⁻¹ from (congr_arg (fun z:Signed=>z.ortho) (tperm_inv r).symm).trans (map_inv Signed.inclusionO _)]; rw [inv_mul_cancel],pol_one]
  have ho : reflectPol t a=b ∨ reflectPol t a= -b:=by
    rcases hr with H|H; exact label_twin r i j k l H.1 H.2
    rw [show b=label G l k from team_swap G _ _]; exact label_twin r i j l k H.1 H.2
  have hs := skew_slot H hy (chain hd ha) (chain hd hb)
  change Slot T a b=0
  have hv := same_slot (tperm r) h hd H (p:=a) (q:=b) hi ha hb; change Slot T (reflectPol t a) (reflectPol t b)=Slot T a b at hv
  rcases ho with hr|hr
  · rw [hr] at hv he; rw [he] at hv; rw [hv] at hs; exact hn hs
  rw [hr,map_neg] at he; rw [hr,show reflectPol t b= -a from neg_eq_iff_eq_neg.mp he,map_neg,map_neg,LinearMap.neg_apply,neg_neg] at hv; rw [hv] at hs; exact hn hs

lemma low_span (V : Submodule ℂ (WickPol G)) (h : G.Simple) : shellSector G 4 ≤ V ↔ 1∈V ∧ ∀ i j : Index,i≤j→label G i j∈V := by
  rw [low_support h,label_span]; simp [BottomOnly,Submodule.span_le]
  intro; constructor; exact fun H i j ht => H ⟨i,j,ht,rfl⟩
  rintro H x ⟨i,j,h,rfl⟩; exact H i j h
lemma kills_four (h : G.Simple) (H : Equivariant d T) (hy : silence G d T) (hd : 4≤d) (hu : T 1=0)
    (ht : ∀ p ∈ shellSector G 4,T p∈shellSector G 4) : ∀ p∈ shellSector G 4,T p=0:=by
  change shellSector G 4 ≤ LinearMap.ker T
  apply (low_span _ h).2 ⟨hu,?_⟩; intro i j hh; let a := label G i j
  have ha : a∈ shellSector G 4 := team_label _ _ le_rfl
  change T a=0; apply probe_axis _ (ht _ ha); change shellSector G 4 ≤ LinearMap.ker (Slot T a)
  rw [low_span _ h]; refine ⟨?_,fun k l hK => (show a=label G i j from rfl).symm ▸ flick i j k l hh hK h H hy hd (ht _ ha)⟩
  have he : Slot T (1:WickPol G) a=0:=by simp [Slot,hu]
  simpa only [LinearMap.mem_ker] using (show Slot T a 1=0 from by simpa only [he,add_zero] using (skew_slot H hy (chain hd ha) (unit_fits (unit_mem _))))
lemma kills_low (h : G.Simple) (hd : d<4) (hu : T 1=0): ∀ p∈shellSector G d,T p=0:= by
  change shellSector G d ≤ LinearMap.ker T; rw [YM.XSpace.Compat.underground h hd,BottomOnly,Submodule.span_singleton_le_iff_mem]; exact hu
end YM.XSpace.Normalize
