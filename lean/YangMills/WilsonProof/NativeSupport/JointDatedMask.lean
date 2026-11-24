import YangMills.WilsonProof.NativeSupport.JointProjectionLedger
import YangMills.WilsonProof.NativeSupport.JointPlantedOld

/-! Forget not-yet-introduced names on a physical ledger. This keeps
every purchased rooted envelope and every coefficient of the exact
measured density whose names have already been introduced. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointShadow
open Function Finset Lattice Wilson RG Marker MeasureTheory MergeProof MergeProof.Accent MergeProof.Menu Extra.Trajectories Packet RGGapR2
open scoped Classical BigOperators
variable {V I:Type} [Fintype V] [DecidableEq V] {G:Gauge} {n:Side}
local notation "B" => Stock.census V
def only (seen:Finset V) (i:V):ℂ:=if i∈seen then 1 else 0
def clip (seen:Finset V) (F:I → Config G n → Marker.Poly (Stock.census V)) (i:I) (Z:Config G n):Marker.Poly (Stock.census V):=
  diagonal (only seen) (F i Z)

theorem mask_part (seen s:Finset V) (P:Poly B) :
    (diagonal (only seen) P).part (tag s)=if s ⊆ seen then P.part (tag s) else 0 := by
  rw [on_part]
  by_cases keep:s ⊆ seen
  · have all_:(∏ i∈s,only seen i)=1 := prod_eq_one (fun i hi=>by rw [only,if_pos (keep hi)])
    rw [if_pos keep,all_,one_mul]
  · obtain ⟨z,hz,no⟩:=Finset.not_subset.mp keep
    rw [if_neg keep,prod_eq_zero hz (if_neg no:only seen z=0),zero_mul]

theorem mask_borne {o:V → Site n} {X:Support n} {t:ℝ} (seen:Finset V) (F:Config G n → Poly B)
    (h:Borne o X F t) : Borne o X (fun Z=>diagonal (only seen) (F Z)) t := by
  refine ⟨fun U Z near flags=>congrArg _ (h.home U Z near flags),fun k U=>congrArg _ (h.turns k U),?_,?_⟩
  · intro p
    change Measurable (fun Z=>(diagonal (only seen) (F Z)).part (tag p.val))
    simp_rw [mask_part]
    split <;> first | exact h.me (tag p.val) | exact measurable_const
  · intro Z p missing
    change (diagonal (only seen) (F Z)).part (tag p.val)=0
    rw [mask_part]
    split
    · exact h.scope Z p missing
    · rfl

theorem clip_ages (seen fresh:Finset V) (separate:Disjoint seen fresh) (F:I → Config G n → Poly B) (i:I) (s:Finset V)
    (live:Vivid (clip seen F) i (tag s)) : Disjoint s fresh := by
  obtain ⟨Z,live⟩:=live
  change (diagonal (only seen) (F i Z)).part (tag s) ≠ 0 at live
  rw [mask_part] at live
  by_cases keep:s ⊆ seen
  · exact separate.mono_left keep
  · exact False.elim (live (if_neg keep))

theorem clip_root [Fintype I] (seen:Finset V) {P:BudgetPoint} {X:I → Support n}
    {F:I → Config G n → Poly B} {w:V → ℝ} {u:ℝ} (budget:RootedSheet P X F w u) : RootedSheet P X (clip seen F) w u := by
  obtain ⟨c,nn,all_,bill⟩:=budget
  refine ⟨c,nn,fun i Z s=>?_,bill⟩
  change ‖(diagonal (only seen) (F i Z)).part (tag s)‖ ≤ _
  rw [mask_part]
  split
  · exact all_ ..
  · rw [norm_zero];exact nn ..

variable (R:Rep G n) (o:V → Site n) (E:Support n → Config G n → Marker.Poly (Stock.census V))
variable (K:Box n → Config G n → Marker.Poly (Stock.census V)) (seen:Finset V)
theorem clip_ledger (original:Rough.Ledger o E K R.p.threshold) :
    Rough.Ledger o (clip seen E) (clip seen K) R.p.threshold ∧
    ∀ Z,play R B (exclaim R.activities B+clip seen K) (fun U=>∑ i,clip seen E i U) Z=
      diagonal (only seen) (play R B (exclaim R.activities B+K) (fun U=>∑ i,E i U) Z) := by
  constructor
  · refine ⟨fun i=>⟨mask_borne seen _ (original.exp i).toBorne,?_,?_⟩,
      fun i=>⟨⟨mask_borne seen _ (original.flag i).1.toBorne,?_⟩,?_⟩⟩
    · exact fun Z live=>(original.exp i).permits Z (fun eq=>live (by rw [clip,eq,map_zero]))
    · intro Z
      change (diagonal (only seen) (E i Z)).part (tag ∅)=0
      simp only [on_part,prod_empty,one_mul];exact (original.exp i).sil Z
    · exact fun Z live=>(original.flag i).1.permits Z (fun eq=>live (by rw [clip,eq,map_zero]))
    · intro Z
      change (diagonal (only seen) (K i Z)).part (tag ∅)=0
      simp only [on_part,prod_empty,one_mul];exact (original.flag i).2 Z
  · intro Z
    let d:=diagonal (only seen)
    have scalar (c:ℂ) (P:Poly B) : d (c • P)=c • d P := MarkerSubstitution.on_smul _ _ _
    have vacuum (i:Box n) : d (exclaim R.activities B i Z)=exclaim R.activities B i Z := by
      change diagonal _ (Poly.send (tag ∅) _)=_
      rw [on_monomial,prod_empty,one_smul]
      rfl
    change _=d _
    simp only [play,field,grid,Poly.pass,Pi.add_apply,scalar,map_sum,map_mul,map_pow,map_prod,map_add,apply_ite d,map_zero,vacuum,clip,d]

end YM.Integration.InletSusceptibility.JointShadow
