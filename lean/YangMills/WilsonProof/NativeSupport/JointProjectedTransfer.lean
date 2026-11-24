import YangMills.WilsonProof.NativeSupport.JointRootedLinear
import YangMills.WilsonProof.NativeSupport.JointNonlinearTariff
import YangMills.WilsonProof.NativeSupport.JointProjection

/-! Reassemble all projected output modes on the original primitive
alphabet. The same coefficient majorant works for every original root.
Old one-switch terms keep the full input exponent. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointShadow
open Function Finset Lattice RG Wilson Marker MergeProof MergeProof.Menu MergeProof.Accent Extra.Trajectories
open FullVolume.Ray PhysicalNext.Repeat PhysicalNext.Repeat.Luna Packet Painted
open scoped BigOperators Classical
variable {I J V:Type} [Fintype I] [Fintype J] [Fintype V] [DecidableEq V]
variable {G:Gauge} {n f:Side} {R:Rep G f}
local notation "C" => Stock.census (Ink V)
local notation "M" => (Stock.census (Ink V)).Mode

private def everyMode (W : Type) [DecidableEq W] [Fintype W] : Finset W ≃ (Stock.census W).Mode :=
  ⟨tag,Subtype.val,fun _=>rfl,fun _=>rfl⟩

theorem projected_transfer (P:BudgetPoint) (X:J → Support n) (F:J → Config G n → Poly C)
    (o:V → Site n) {e t A D bill r τ U:ℝ} (aa:1 ≤ A) (dd:1 ≤ D) (tt:0 ≤ τ)
    (w:V → ℝ) (hw:∀ x,0 < w x) (fresh:Finset V)
    (scope:∀ j,Borne (o ∘ Prod.fst) (X j) (F j) t)
    (full:Towed (weight w A D fresh) X F P.B e bill)
    (q:I → Hat C R) (L:I → sun → J → Config G n → ℂ)
    (single:∀ i,RollsUp P X (L i) r e (τ*(‖((sumFee (q i) (weight w A D fresh):ℝ):ℂ)‖*load (q i).M)))
    (score:∀ j Z (p:M),p.val.Nonempty → ¬gains fresh p.val →
      (F j Z).part p=∑ i,L i Jams.tip j Z*(sing (q i) (weight w A D fresh)).part p)
    (old_bill:∀ y:V,
      (∑ i:I with y∈(q i).s.val.image Prod.fst ∧ ¬gains fresh (q i).s.val,
        sumFee (q i) (fun v:Ink V=>w v.1)*load (q i).M) ≤ U) :
    ∃ c:J → Finset V → ℝ, (∀ j S,0 ≤ c j S) ∧
      (∀ j Z S,‖(project (F j Z)).part (tag S)‖ ≤ c j S) ∧
      ∀ y:V,(∑ j,Real.exp (e*coverNumber P.B (X j))*
        ∑ S:Finset V with y∈S,Poly.toll w (tag S)*c j S) ≤ τ*U+bill/min D (A^2) := by
  let v:=Painted.weight w A D fresh
  have positiveA:0 < A :=zero_lt_one.trans_le aa
  have positiveD:0 < D :=zero_lt_one.trans_le dd
  have hv (x:Ink V) : 0 < v x := by
    have z:=hw x.1
    dsimp only [v,Painted.weight]
    split <;> split <;> positivity
  let b (p:M) := Poly.toll (fun x:Ink V=>w x.1) p
  have pb (p:M) : 0 ≤ b p := (Poly.worth (fun x:Ink V=>hw x.1) p).le
  obtain ⟨ell,ep,ev,eb⟩:=NativeSwitch.linear_modes q v hv P X L e r τ single
  obtain ⟨nn,np,nv,nb⟩:=rooted_nonlinear aa dd w hw fresh o F scope full
  let cap (j:J) (s:Finset (Ink V)) := if s.Nonempty ∧ ¬gains fresh s then ell j (tag s) else nn j (tag s)
  let c (j:J) (S:Finset V) := ∑ s:Finset (Ink V) with faithful s ∧ s.image Prod.fst=S,cap j s
  have cp j s : 0 ≤ cap j s := by unfold cap;split;exact ep ..;exact np ..
  refine ⟨c,fun j S=>sum_nonneg fun s _=>cp j s,?_,?_⟩
  · intro j Z S
    rw [projected_part]
    refine (norm_sum_le _ _).trans (sum_le_sum fun s _=>?_ )
    change ‖(F j Z).part (tag s)‖ ≤ cap j s
    unfold cap
    split
    next old =>
      rw [score j Z (tag s) old.1 old.2]
      exact ev Jams.tip j Z (tag s)
    next => exact nv j Z (tag s)
  · intro y
    let old (p:M) := y∈p.val.image Prod.fst ∧ ¬gains fresh p.val
    let newHit (p:M) := y∈p.val.image Prod.fst ∧ gains fresh p.val
    let oldSet:=univ.filter old
    let newSet:=univ.filter newHit
    let d (j:J) := Real.exp (e*coverNumber P.B (X j))
    let eo j:=∑ p∈oldSet,b p*ell j p
    let en j:=∑ p∈newSet,b p*nn j p
    have oldTotal : (∑ j,d j*eo j) ≤ τ*U := by
      apply (eb (fun z=>w z.1) (fun z=>hw z.1) oldSet).trans
      apply mul_le_mul_of_nonneg_left _ tt
      simpa only [oldSet,mem_filter,mem_univ,true_and,old] using old_bill y
    have newTotal : (∑ j,d j*en j) ≤ bill/min D (A^2) := by
      apply (le_div_iff₀ (lt_min positiveD (sq_pos_of_pos positiveA))).mpr
      rw [mul_comm]
      simpa only [d,en,newSet,newHit,b,mul_comm (Real.exp _) _] using nb y
    have cell (j:J) : (∑ S:Finset V with y∈S,Poly.toll w (tag S)*c j S) ≤ eo j+en j := by
      change (∑ S:Finset V with y∈S,Poly.toll w (tag S)*
        ∑ s:Finset (Ink V) with faithful s ∧ s.image Prod.fst=S,cap j s) ≤ _
      rw [projected_mass]
      change _ ≤ (∑ p:M with old p,b p*ell j p)+(∑ p:M with newHit p,b p*nn j p)
      simp only [sum_filter]
      rw [←(everyMode (Ink V)).sum_comp (fun p:M=>if old p then b p*ell j p else 0),
        ←(everyMode (Ink V)).sum_comp (fun p:M=>if newHit p then b p*nn j p else 0),←sum_add_distrib]
      apply sum_le_sum
      intro s _
      change (if faithful s ∧ y∈s.image Prod.fst then b (tag s)*cap j s else 0) ≤
        (if y∈s.image Prod.fst ∧ ¬gains fresh s then b (tag s)*ell j (tag s) else 0)+(if y∈s.image Prod.fst ∧ gains fresh s then b (tag s)*nn j (tag s) else 0)
      by_cases hit:y∈s.image Prod.fst
      · have ne : s.Nonempty := by obtain ⟨a,ha,_⟩:=mem_image.mp hit; exact ⟨a,ha⟩
        by_cases g:gains fresh s <;> by_cases f₀:faithful s <;>
          simp [hit,g,f₀,cap,ne,mul_nonneg (pb _) (ep ..),mul_nonneg (pb _) (np ..)]
      · simp [hit]
    calc
      _ ≤ ∑ j,d j*(eo j+en j) := sum_le_sum fun j _=>mul_le_mul_of_nonneg_left (cell j) (Real.exp_pos _).le
      _ = (∑ j,d j*eo j)+(∑ j,d j*en j) := by simp only [mul_add,sum_add_distrib]
      _ ≤ _ := add_le_add oldTotal newTotal

end YM.Integration.InletSusceptibility.JointShadow
