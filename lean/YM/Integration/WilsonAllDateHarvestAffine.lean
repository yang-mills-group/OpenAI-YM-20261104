import YM.RG05Readout.Many.Run
import YM.MergeProof.Pitch

/-! The physical census has at most three occupied slots on every allowed mode.
Two higher marked entries therefore never multiply in the restored density.
All scalar and singleton hard entries stay in their true compatible gas. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section

namespace YM.Integration.WilsonAllDateHarvestAffine

open Finset Lattice Wilson RG Marker MergeProof MergeProof.Accent Extra.Histories RG05Readout RG05Readout.Many RG05Readout.Native RG05Readout.Address RG05Readout.View
open scoped BigOperators Classical

variable {V : Type*} [DecidableEq V] {J : Census V}

def Three (J : Census V) : Prop := ∀ s : J.Mode, s.val.card ≤ 3

private def Mixed (x : Poly J) : Prop := ∀ s:J.Mode, s.val.card < 2 → x.part s=0

private theorem mixed {x : Poly J} (h : rises x) : Mixed x := by
  intro s hs
  by_contra nz
  exact (Nat.not_le_of_gt hs) (h s nz)

private theorem mzero : Mixed (0 : Poly J) := fun _ _ => rfl

private theorem mplus {x y : Poly J} (h : Mixed x) (g : Mixed y) : Mixed (x+y) := by
  intro s hs
  simp [Poly.part_plus,h s hs,g s hs]

private theorem msub {x y : Poly J} (h : Mixed x) (g : Mixed y) : Mixed (x-y) := by
  intro s hs
  change x.part s-y.part s=0
  rw [h s hs,g s hs,sub_self]

private theorem mmul (x : Poly J) {y : Poly J} (h : Mixed y) : Mixed (x*y) := by
  intro s hs
  rw [Poly.part_mul]
  apply sum_eq_zero
  intro a _
  apply sum_eq_zero
  intro b _
  split_ifs with active
  · have count : s.val.card=a.val.card+b.val.card := by
      rw [← active.2,card_union_of_disjoint active.1]
    rw [h b (by omega),mul_zero]
  · rfl

private theorem square (cap : Three J) {x y : Poly J} (h : Mixed x) (g : Mixed y) : x*y=0 := by
  ext s
  rw [Poly.part_nil,Poly.part_mul]
  apply sum_eq_zero
  intro a _
  apply sum_eq_zero
  intro b _
  split_ifs with active
  · have count : s.val.card=a.val.card+b.val.card := by
      rw [← active.2,card_union_of_disjoint active.1]
    have fits:=cap s
    by_cases ha:a.val.card<2
    · rw [h a ha,zero_mul]
    · rw [g b (by omega),mul_zero]
  · rfl

private def Line (f : ℂ → Poly J) : Prop := ∃ a b, Mixed b ∧ ∀ t, f t=a+t • b

private theorem constant (p : Poly J) : Line (fun _ : ℂ=>p) :=
  ⟨p,0,mzero,fun _=>by simp⟩

private theorem plus {f g : ℂ → Poly J} (h : Line f) (k : Line g) : Line (fun z=>f z+g z) := by
  obtain ⟨a,b,hb,hf⟩:=h
  obtain ⟨c,d,hd,hg⟩:=k
  exact ⟨a+c,b+d,mplus hb hd,fun z=>by dsimp only; rw [hf,hg,smul_add]; abel⟩

private theorem times (cap : Three J) {f g : ℂ → Poly J} (h : Line f) (k : Line g) :
    Line (fun z=>f z*g z) := by
  obtain ⟨a,b,hb,hf⟩:=h
  obtain ⟨c,d,hd,hg⟩:=k
  have zero:=square cap hb hd
  refine ⟨a*c,a*d+c*b,mplus (mmul _ hd) (mmul _ hb),?_⟩
  intro z
  dsimp only
  rw [hf,hg,add_mul,mul_add,mul_add,mul_smul_comm,smul_mul_assoc,smul_mul_assoc,
    mul_smul_comm,zero,smul_zero,smul_zero,add_zero,smul_add,mul_comm b c]
  abel

private theorem multiplied {f : ℂ → Poly J} (h : Line f) (v : ℂ) : Line (fun z=>v • f z) := by
  obtain ⟨a,b,hb,hf⟩:=h
  refine ⟨v • a,v • b,?_,fun z=>by dsimp only; rw [hf,smul_add,smul_comm v z]⟩
  intro s hs
  rw [Poly.part_smul,hb s hs,mul_zero]

private theorem summed {ι : Type*} (s : Finset ι) (f : ι → ℂ → Poly J)
    (h : ∀i∈s,Line (f i)) : Line (fun z=>∑ i∈s,f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [sum_empty] using constant (0:Poly J)
  | insert i s hs ih =>
    simp only [sum_insert hs]
    exact plus (h i (mem_insert_self ..)) (ih (fun j hj=>h j (mem_insert_of_mem hj)))

private theorem product (cap : Three J) {ι : Type*} (s : Finset ι) (f : ι → ℂ → Poly J)
    (h : ∀i∈s,Line (f i)) : Line (fun z=>∏ i∈s,f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [prod_empty] using constant (1:Poly J)
  | insert i s hs ih =>
    simp only [prod_insert hs]
    exact times cap (h i (mem_insert_self ..)) (ih (fun j hj=>h j (mem_insert_of_mem hj)))

private theorem power (cap : Three J) {f : ℂ → Poly J} (h : Line f) (n : ℕ) :
    Line (fun z=>f z^n) := by
  induction n with
  | zero => simpa only [pow_zero] using constant (1:Poly J)
  | succ n ih => simpa only [pow_succ] using times cap ih h

variable [Fintype V]

private theorem exponential (cap : Three J) {f : ℂ → Poly J} (h : Line f) :
    Line (fun z=>Poly.pass (f z)) := by
  unfold Poly.pass
  exact summed _ _ (fun i _=>multiplied (power cap h i) _)

def blend {E : Type*} [AddCommGroup E] [Module ℂ E] (a b : E) (t : ℂ) : E :=
  a+t • (b-a)

omit [Fintype V] in
private theorem endpoints {f : ℂ → Poly J} (h : Line f) (t:ℂ) : f t=blend (f 0) (f 1) t := by
  obtain ⟨a,b,_,h⟩:=h
  simp [blend,h,add_sub_cancel_left]

variable {G : Gauge} {n : Side}

omit [Fintype V] in
private theorem gas (cap : Three J) (f : Box n → ℂ → Poly J) (h : ∀i,Line (f i)) (flags : Support n) :
    Line (fun z=>field (fun i=>f i z) flags) := by
  unfold field
  apply summed
  intro s _
  unfold grid
  split_ifs with live
  · exact product cap s f (fun i _=>h i)
  · exact constant 0

variable (P : Rep G n) (Φ : V → Config G n → ℂ) (ω : V → Box n → Config G n → ℂ)
variable {H S : Support n → Config G n → Poly J} {K T : Box n → Config G n → Poly J}

theorem original (cap : Three J)
    (hH : ∀i U,rises (H i U)) (hS : ∀i U,rises (S i U))
    (hK : ∀i U,rises (K i U)) (hT : ∀i U,rises (T i U)) (z : ℂ) (U : Config G n) :
    restore P Φ ω (fun i X=>blend (H i X) (S i X) z) (fun i X=>blend (K i X) (T i X) z) U
      = blend (restore P Φ ω H K U) (restore P Φ ω S T U) z := by
  let f (t:ℂ):=restore P Φ ω (fun i X=>blend (H i X) (S i X) t) (fun i X=>blend (K i X) (T i X) t) U
  have m (i:Support n): Line (fun t=>blend (H i U) (S i U) t) :=
    ⟨H i U,S i U-H i U,msub (mixed (hS i U)) (mixed (hH i U)),fun _=>rfl⟩
  have k (i:Box n): Line (fun t=>blend (K i U) (T i U) t) :=
    ⟨K i U,T i U-K i U,msub (mixed (hT i U)) (mixed (hK i U)),fun _=>rfl⟩
  have line : Line f := by
    apply multiplied
    apply times cap
    · exact exponential cap (plus (constant _) (summed _ _ (fun i _=>m i)))
    · exact gas cap _ (fun i=>plus (constant _) (k i)) _
  have e0 : f 0=restore P Φ ω H K U := by simp [f,blend]
  have e1 : f 1=restore P Φ ω S T U := by simp [f,blend,add_sub_cancel]
  exact (endpoints line z).trans (by rw [e0,e1])

theorem actual {C:Family G} {b m j per:ℕ} (o:Fin 3→Site (C.side b per)) (E:Fin 3→Motion)
    (roster:Census (Fin 3)) (bm:b ≤ m) (mj:m ≤ j) :
    Three (Mine.masts o E bm (barren o E roster m) j) := by
  intro s
  have inclusion:=Mine.masts_le o E bm (barren o E roster m) roster (Finset.filter_subset ..) mj
  have admitted:=inclusion s.property
  have lit:= (Finset.mem_filter.mp admitted).2
  have count:=Lit.keep_count lit
  have three:=Finset.card_le_univ lit.climb.val
  simpa only [count,Fintype.card_fin] using three

end YM.Integration.WilsonAllDateHarvestAffine
