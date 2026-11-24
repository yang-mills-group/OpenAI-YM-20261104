import YangMills.WilsonProof.NativeSupport.JointBornIntake
import YangMills.WilsonProof.NativeSupport.JointPhysicalDock

/-! Charge the actual mounted real and imaginary switches at the old
full support price. Each painted old word is one original word. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Painted
open Function Finset Lattice RG Wilson Marker MergeProof MergeProof.Menu Packet
open scoped Classical BigOperators
variable {V:Type} [Fintype V] [DecidableEq V]
local notation "C" => Stock.census (Ink V)
local notation "M" => (Stock.census (Ink V)).Mode

def oldCap (c:Finset V → ℝ) (p:M) : ℝ :=
  if p.val=wear (p.val.image Prod.fst) then c (p.val.image Prod.fst) else 0

theorem old_cap_root (c:Finset V → ℝ) (w:V → ℝ) (y:V) :
    (∑ p:M with y∈p.val.image Prod.fst,Poly.toll (fun x:Ink V=>w x.1) p*oldCap c p) =
    ∑ s:Finset V with y∈s,Poly.toll w (tag s)*c s := by
  let base (p:M) := Poly.toll (fun x:Ink V=>w x.1) p
  let keep (p:M) := y∈p.val.image Prod.fst ∧ p.val=wear (p.val.image Prod.fst)
  calc
    _ = ∑ p:M with keep p,base p*c (p.val.image Prod.fst) := by
      simp only [sum_filter]
      apply sum_congr rfl
      intro p _
      change (if y∈p.val.image Prod.fst then base p*oldCap c p else 0)=
        if y∈p.val.image Prod.fst ∧ p.val=wear (p.val.image Prod.fst) then base p*c (p.val.image Prod.fst) else 0
      by_cases h:y∈p.val.image Prod.fst
      · by_cases he:p.val=wear (p.val.image Prod.fst)
        · rw [if_pos h,oldCap,if_pos he,if_pos ⟨h,he⟩]
        · rw [if_pos h,oldCap,if_neg he,if_neg (fun z=>he z.2),mul_zero]
      · rw [if_neg h,if_neg (fun z=>h z.1)]
    _ = _ := by
      refine sum_bij' (fun p _=>p.val.image Prod.fst) (fun s _=>tag (wear s)) ?_ ?_ ?_ ?_ ?_
      · intro p hp; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hp).2.1⟩
      · intro s hs
        exact mem_filter.mpr ⟨mem_univ _,by simpa only [keep,tag,wear_image, and_true] using (mem_filter.mp hs).2⟩
      · intro p hp
        exact Subtype.ext (mem_filter.mp hp).2.2.symm
      · intro s _
        exact wear_image s
      · intro p hp
        let s:=p.val.image Prod.fst
        have eq:p=tag (wear s) := Subtype.ext (mem_filter.mp hp).2.2
        change base p*c s=Poly.toll w (tag s)*c s
        have cost : base p=Poly.toll w (tag s) := by
          change Poly.toll (fun x:Ink V=>w x.1) p=_
          calc _ = Poly.toll (fun x:Ink V=>w x.1) (tag (wear s)) := congrArg _ eq
               _ = Poly.toll w (tag s) := by simpa only [wear_image] using (projected_toll w (wear s) (wear_kept s)).symm
        rw [cost]

variable {I:Type} [Fintype I] {G:Gauge} {n:Side} {R:Rep G n}
theorem mounted_old_bill (X:I → Support n) (F:I → Config G n → Poly C) (q:VividId F → Hat C R)
    (modes:∀ i,(q i).s=i.2.1.val) (cap:I → Finset V → ℝ) (nn:∀ i s,0 ≤ cap i s) (w:V → ℝ) (hw:∀ v,0 < w v)
    (fresh:Finset V) (charged:∀ i (p:{s:M // Vivid F i s}),¬gains fresh p.val.val →
      (∑ j:Bool,sumFee (q ⟨i,p,j⟩) (fun v:Ink V=>w v.1)*load (q ⟨i,p,j⟩).M) ≤
        2*R.p.mass (X i) (Poly.toll (fun v:Ink V=>w v.1) p.val*oldCap (cap i) p.val))
    (y:V) :
    (∑ i:VividId F with y∈(q i).s.val.image Prod.fst ∧ ¬gains fresh (q i).s.val,
      sumFee (q i) (fun v:Ink V=>w v.1)*load (q i).M) ≤
      2*∑ i, Real.exp (R.p.supportExponent*coverNumber R.p.B (X i))*
        ∑ s:Finset V with y∈s,Poly.toll w (tag s)*cap i s := by
  let base (p:M):= Poly.toll (fun v:Ink V=>w v.1) p
  let price (i:VividId F) :=sumFee (q i) (fun v:Ink V=>w v.1)*load (q i).M
  let b i (p:M) := 2*R.p.mass (X i) (base p*oldCap (cap i) p)
  have pos i p : 0 ≤ b i p := by
    have cp : 0 ≤ oldCap (cap i) p := by unfold oldCap;split; exact nn ..; rfl
    have wp : 0 ≤ base p := (Poly.worth (fun v:Ink V=>hw v.1) p).le
    dsimp only [b,BudgetPoint.mass]
    positivity
  rw [sum_filter,mul_sum]
  change (∑ i:Σ k, {p:M // Vivid F k p} × Bool,
    if y∈(q i).s.val.image Prod.fst ∧ ¬gains fresh (q i).s.val then price i else 0) ≤ _
  rw [Fintype.sum_sigma]
  apply sum_le_sum
  intro i _
  rw [Fintype.sum_prod_type]
  let eligible (p:M):=y∈p.val.image Prod.fst
  let upper (p:M) := if eligible p then b i p else 0
  calc
    _ ≤ ∑ p : {s:M // Vivid F i s},upper p.val := by
      apply sum_le_sum
      intro p _
      simp_rw [modes]
      change (∑ j:Bool,if eligible p.val ∧ ¬gains fresh p.val.val then price ⟨i,p,j⟩ else 0) ≤ upper p.val
      by_cases hit:eligible p.val
      · by_cases g:gains fresh p.val.val
        · simpa only [hit,g,not_true_eq_false,and_false,if_false,sum_const_zero,upper,if_true] using pos i p.val
        · simpa only [hit,g,not_false_eq_true,and_self,if_true,upper,price,b,base] using charged i p g
      · simp only [upper,hit,false_and,if_false,sum_const_zero,le_refl]
    _ ≤ ∑ p:M,upper p := by
      rw [← Finset.sum_subtype (p:=Vivid F i) (univ.filter (Vivid F i)) (fun p=>by simp) upper]
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _=>by unfold upper;split; exact pos i p; rfl)
    _ = 2*(Real.exp (R.p.supportExponent*coverNumber R.p.B (X i))*∑ s:Finset V with y∈s,Poly.toll w (tag s)*cap i s) := by
      rw [←old_cap_root (cap i) w y,←mul_assoc,mul_sum,sum_filter]
      apply sum_congr rfl
      intro p _
      by_cases h:y∈p.val.image Prod.fst
      · simp only [upper,eligible,h,if_true,b,BudgetPoint.mass,base]; ring
      · simp only [upper,eligible,h,if_false]

end YM.Integration.InletSusceptibility.Painted
