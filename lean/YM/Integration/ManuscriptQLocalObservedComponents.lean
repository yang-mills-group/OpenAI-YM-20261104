import YM.Integration.ManuscriptQLocalIntegratedTicket

/-! The purchased material terms are evaluated on independently chosen actual
coarse fields. Every original outer gas activity occurs inside its own true
conditional integral, before taking a norm of the material at that field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalObservedComponents
open Filter Function Finset Lattice Wilson RG Tree Pressure Pressure.Stores ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Push Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Next.Scheduling AnalyticBridge VerifiedReset
open MergeProof Marker Extra.Multi LocalLTE PhysicalNext.Repeat.Daisy
open scoped Classical Topology BigOperators
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {R:Rep G f}
  {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W x μ a:ℝ} {o:Target.Order G W}
  (H:Cash W x μ L Q o a T R) (χ:Push.SectorMeasure.Chi)
  {V ι:Type} [DecidableEq V] {Γ:Marker.Census V} (M:ι→Menu.Hat Γ R)
  {C d rv s A v y B e:ℝ} {j k:ℕ} (N:Captain H j C d rv s A v y B e k χ)
  (host:HostQ H N.conduit A B k) (Z:BudgetPoint) (ht:Z.threshold=Pressure.temp x)
  (hord:Z.order≤j) (n:ℕ) (hpower:Z.power≤n)

include host ht hord hpower in
lemma value (z:Fan.Stars H (fun i => (M i).M)) (o:Site c) (ho:o∈Captain.reachability z.1) (U:Config G c) :
    |ManuscriptQLocalIntegratedTicket.activity H χ M z.1 z.2 U|≤
      if ManuscriptQLocalForcedClusters.alive H χ (fun i => (M i).M) z then Captain.wife N z.1 (fun i => (M i).M) z.2 n else 0 := by
  have receipt:=ManuscriptQLocalForcedClusters.differentiated H χ (fun i => (M i).M) N host z Z ht hord n hpower
  have paid:=receipt.2.2 o ho
  have equals:ManuscriptQLocalIntegratedTicket.activity H χ M z.1 z.2 U=RG.masked Z.threshold
      (Captain.reachability z.1) (Captain.wingTerm (H:=H) (χ:=χ) z.1 (fun i => (M i).M) z.2) U:=congrFun receipt.1 U
  rw [equals]
  by_cases good:RG.Healthy Z.threshold (Captain.reachability z.1) U
  · rw [RG.masked_eq _ _ _ _ good]
    exact paid.2 U good [] (Nat.zero_le _) (by simp)
  · rw [RG.masked_ne _ _ _ _ good,abs_zero];exact paid.1


def derivative (z:Fan.Stars H (fun i => (M i).M)) (U:Config G c) (l:List (Directions G c)) : ℝ :=
  if RG.Healthy Z.threshold (Captain.reachability z.1) U then
    RG.leftDerivs (Captain.wingTerm (H:=H) (χ:=χ) z.1 (fun i => (M i).M) z.2) l U else 0

include host ht hord hpower in
lemma derivative_le (z:Fan.Stars H (fun i => (M i).M)) (o:Site c) (ho:o∈Captain.reachability z.1)
    (U:Config G c) (l:List (Directions G c)) (hl:l.length≤Z.order) (hdir:∀A∈l,Z.dirBound o A) :
    |derivative H χ M Z z U l|≤
      if ManuscriptQLocalForcedClusters.alive H χ (fun i => (M i).M) z then Captain.wife N z.1 (fun i => (M i).M) z.2 n else 0 := by
  have price:=(ManuscriptQLocalForcedClusters.differentiated H χ (fun i => (M i).M) N host z Z ht hord n hpower).2.2 o ho
  by_cases good:RG.Healthy Z.threshold (Captain.reachability z.1) U
  · rw [derivative,if_pos good];exact price.2 U good l hl hdir
  · rw [derivative,if_neg good,abs_zero];exact price.1

theorem root_bound (w:V→ℝ) (hw:∀v,0<w v) (material:Fan.Stars H (fun i => (M i).M)→Poly Γ)
    (keep:Fan.Stars H (fun i => (M i).M)→Prop) {γ u:ℝ}
    (price:Ac.Hit (fun z:Fan.Stars H (fun i => (M i).M)=>Captain.reachability z.1) (radiusB x)
      (fun z=>if keep z ∧ ManuscriptQLocalForcedClusters.alive H χ (fun i => (M i).M) z then
        Poly.price w (material z)*Captain.wife N z.1 (fun i => (M i).M) z.2 n else 0) γ u)
    (root:Site c) (sample:Fan.Stars H (fun i => (M i).M)→ℝ)
    (coupon:∀z,root∈Captain.reachability z.1→ |sample z|≤
      if ManuscriptQLocalForcedClusters.alive H χ (fun i => (M i).M) z then Captain.wife N z.1 (fun i => (M i).M) z.2 n else 0) :
    SumBudget (fun z:Fan.Stars H (fun i => (M i).M)=>if root∈Captain.reachability z.1 then
      (if keep z then Poly.price w ((sample z:ℂ) • material z) else 0)*
        Real.exp (γ*coverNumber (radiusB x) (Captain.reachability z.1)) else 0) u := by
  apply budget_mono (price root)
  · intro z
    split_ifs <;> first | exact le_rfl | exact mul_nonneg (Poly.nonnegative hw _) (Real.exp_pos _).le | simp only [zero_mul, le_refl]
  · intro z
    by_cases seen:root∈Captain.reachability z.1
    · simp only [if_pos seen]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      by_cases hk:keep z
      · rw [if_pos hk,Poly.adapted,Complex.norm_real,Real.norm_eq_abs]
        have bound:=coupon z seen
        by_cases live:ManuscriptQLocalForcedClusters.alive H χ (fun i => (M i).M) z
        · rw [if_pos ⟨hk,live⟩];rw [if_pos live] at bound
          exact (mul_le_mul_of_nonneg_right bound (Poly.nonnegative hw _)).trans_eq (mul_comm _ _)
        · rw [if_neg (fun h=>live h.2)];rw [if_neg live] at bound
          exact (mul_le_mul_of_nonneg_right bound (Poly.nonnegative hw _)).trans_eq (zero_mul _)
      · rw [if_neg hk,if_neg (fun h=>hk h.1)]
    · simp only [if_neg seen,le_refl]

include host ht hord hpower in
/-- Rooted physical price after inserting a possibly different actual coarse
configuration in every complete integrated ticket. -/
theorem bought (w:V→ℝ) (hw:∀v,0<w v) (material:Fan.Stars H (fun i => (M i).M)→Poly Γ)
    (keep:Fan.Stars H (fun i => (M i).M)→Prop) {γ u:ℝ}
    (price:Ac.Hit (fun z:Fan.Stars H (fun i => (M i).M)=>Captain.reachability z.1) (radiusB x)
      (fun z=>if keep z ∧ ManuscriptQLocalForcedClusters.alive H χ (fun i => (M i).M) z then
        Poly.price w (material z)*Captain.wife N z.1 (fun i => (M i).M) z.2 n else 0) γ u)
    (U:Fan.Stars H (fun i => (M i).M) → Config G c) :
    Ac.Hit (fun z:Fan.Stars H (fun i => (M i).M)=>Captain.reachability z.1) (radiusB x)
      (fun z=>if keep z then Poly.price w
        ((ManuscriptQLocalIntegratedTicket.activity H χ M z.1 z.2 (U z):ℂ) • material z) else 0) γ u := fun root=>root_bound H χ M N n w hw material keep price root
      (fun z=>ManuscriptQLocalIntegratedTicket.activity H χ M z.1 z.2 (U z))
      (fun z hz=>value H χ M N host Z ht hord n hpower z root hz (U z))

/-- Evaluated rooted cut. Values use the true integrated activity on every
configuration, and derivatives use each original supported healthy chart. -/
def Tested (w:V→ℝ) (material:Fan.Stars H (fun i => (M i).M)→Poly Γ) (keep:Fan.Stars H (fun i => (M i).M)→Prop) (γ u:ℝ) : Prop :=
  (∀U:Fan.Stars H (fun i => (M i).M) → Config G c,Ac.Hit (fun z:Fan.Stars H (fun i => (M i).M)=>Captain.reachability z.1) (radiusB x)
    (fun z=>if keep z then Poly.price w
      ((ManuscriptQLocalIntegratedTicket.activity H χ M z.1 z.2 (U z):ℂ) • material z) else 0) γ u) ∧
  ∀(root:Site c) (U:Fan.Stars H (fun i => (M i).M) → Config G c) (l:Fan.Stars H (fun i => (M i).M)→List (Directions G c)),
    (∀z,root∈Captain.reachability z.1→ (l z).length≤Z.order ∧ ∀A∈l z,Z.dirBound root A) →
    SumBudget (fun z:Fan.Stars H (fun i => (M i).M)=>if root∈Captain.reachability z.1 then
      (if keep z then Poly.price w ((derivative H χ M Z z (U z) (l z):ℂ) • material z) else 0)*
        Real.exp (γ*coverNumber (radiusB x) (Captain.reachability z.1)) else 0) u

include host ht hord hpower in
theorem paid (w:V→ℝ) (hw:∀v,0<w v) (material:Fan.Stars H (fun i => (M i).M)→Poly Γ)
    (keep:Fan.Stars H (fun i => (M i).M)→Prop) {γ u:ℝ}
    (price:Ac.Hit (fun z:Fan.Stars H (fun i => (M i).M)=>Captain.reachability z.1) (radiusB x)
      (fun z=>if keep z ∧ ManuscriptQLocalForcedClusters.alive H χ (fun i => (M i).M) z then
        Poly.price w (material z)*Captain.wife N z.1 (fun i => (M i).M) z.2 n else 0) γ u) :
    Tested H χ M Z w material keep γ u :=
  ⟨bought H χ M N host Z ht hord n hpower w hw material keep price,
   fun root U l allowed=>root_bound H χ M N n w hw material keep price root
     (fun z=>derivative H χ M Z z (U z) (l z)) (fun z seen=>derivative_le H χ M N host Z ht hord n hpower
       z root seen (U z) (l z) (allowed z seen).1 (allowed z seen).2)⟩

end YM.Integration.ManuscriptQLocalObservedComponents
