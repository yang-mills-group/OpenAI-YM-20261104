import YM.Integration.WilsonOriginalFiniteSignedWage
import YM.Integration.WilsonOriginalJointDeckLocality

/-! The coupled mixed jet of each actual original marked field, separated by its genuine lifted origins and the center of its paid word. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalRelativeMixedFields
open Filter Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry QuadraticLocal.Sunrise Stationary
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalPaidWalkCover WilsonOriginalCenteredSeamSalary WilsonOriginalSuspendedWord WilsonEmittedRootedJetWage
open WilsonOriginalSuspendedTensor WilsonOriginalSuspendedFootprint WilsonOriginalNamedRelativeRows
open scoped Classical BigOperators ContDiff
variable {G:Gauge} {n N:Side} {V X ι:Type} [DecidableEq V] {o:Passport n V} {J:Census V}
    (h:n.val∣N.val) (M:ι→Row o J G X) (t:X) (s:J.Mode) (x:Site N)
abbrev Choice (s:Finset V) (n N:Side) (G:Gauge) (r:ℕ):=
  Fin (Pages n N) × (s→Fin (Pages n N)) × (Fin r→Slot G N)

def rootset (o:Passport n V) (s:Finset V) (u:s→Fin (Pages n N)):Finset (Site N):=
  univ.image fun v:s=>(page h (o.origin v.val) (u v)).val

def span (o:Passport n V) (s:Finset V) (x:Site N) {r:ℕ} (u:Choice s n N G r):ℕ:=
  radius x (trace u.2.2 ∪ rootset h o s u.2.1)

def selected {r:ℕ} (u:Choice s.val n N G r) (i:ι):Prop:=
  (M i).mode=s ∧ (row h (M i) u.1).center=x ∧ assigned h M s.val i u.1=u.2.1

def joined {r:ℕ} (j:ℕ) (u:Choice s.val n N G r) (z:Joint G N):ℂ:=
  (z.1^j:ℝ)*WilsonOriginalMixedCoveredRead.field h M t u.1 (selected h M s x u) z

def embed (s:Finset V) (r:ℕ): (Σ _:ι,Choice s n N G r) ↪
    (Σ _:WilsonOriginalCoveredMixedRoster.Item ι n N G r,(s→Fin (Pages n N))) where
  toFun v:=⟨⟨⟨v.1,v.2.1⟩,v.2.2.2⟩,v.2.2.1⟩
  inj':=by rintro ⟨i,p,u,d⟩ ⟨k,q,v,f⟩ e;cases e;rfl

theorem reaches {r:ℕ} (u:Choice s.val n N G r) (i:ι) (matchRow: selected h M s x u i):
    span h o s.val x u ≤ radius (row h (M i) u.1).center
      (targets (passport h (M i) u.1) s.val (trace u.2.2)):=by
  rw [matchRow.2.1]
  unfold span radius
  apply sup_mono
  intro y hy
  rcases mem_union.mp hy with a|b
  · exact mem_union_left _ a
  · obtain ⟨v,_,eq⟩:=mem_image.mp b
    apply mem_union_right _ (mem_biUnion.mpr ⟨v.val,v.prop,?_⟩)
    rw [←eq,←matchRow.2.2]
    have S:=active_page h (M i) u.1 v.val
    change (page h (o.origin v.val) (index h (M i) u.1 v.val)).val ∈ (passport h (M i) u.1).support v.val
    rw [S]
    exact (passport h (M i) u.1).born v.val

theorem original {w:V→ℝ} {grades:V→ℕ} {σ C:ℝ} {order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf) (hs:0<σ) (j r:ℕ):
    (∑u:Choice s.val n N G r,Poly.toll w s * Real.exp ((σ/2)*span h o s.val x u) *
      ‖WilsonOriginalJointDeckMotion.entry r (joined h M t s x j u) u.2.2‖) ≤ fee G σ r*C:=by
  let W:=fun u:Choice s.val n N G r=>Poly.toll w s * Real.exp ((σ/2)*span h o s.val x u)
  let m:=fun (i:ι) (u:Choice s.val n N G r)=>if selected h M s x u i then WilsonOriginalSuspendedFootprint.at (row h (M i) u.1) t j r u.2.2 else 0
  let out:=fun u:Choice s.val n N G r=>WilsonOriginalJointDeckMotion.entry r (joined h M t s x j u) u.2.2
  have non:0≤Poly.toll w s:=prod_nonneg fun v _=>(stock.positive v).le
  have priced (u:Choice s.val n N G r):0≤W u:=mul_nonneg non (Real.exp_pos _).le
  have paid (u:Choice s.val n N G r):HasSum (fun i=>m i u) (out u):=
    WilsonOriginalSuspendedCoveredRead.original h M t u.1 (selected h M s x u) stock hs j r u.2.2
  let E:=embed (ι:=ι) (G:=G) (n:=n) (N:=N) s.val r
  let a:=fun y:Σ (_:WilsonOriginalCoveredMixedRoster.Item ι n N G r),(s.val→Fin (Pages n N))=>
    if assigned h M s.val y.1.1.1 y.1.1.2=y.2 then
      WilsonOriginalCoveredMixedRoster.wage h M w x s.val t j r σ y.1 else 0
  have wide:SumBudget a (fee G σ r*C):=WilsonOriginalCoveredMixedRoster.named h M stock hs x s.val t j r
  have one (y:Σ _:ι,Choice s.val n N G r):W y.2*‖m y.1 y.2‖ ≤ a (E y):=by
    obtain ⟨i,u⟩:=y
    change W u*‖m i u‖ ≤ a (E ⟨i,u⟩)
    by_cases matchRow:selected h M s x u i
    · have sub:s.val⊆(row h (M i) u.1).mode.val:=by change s.val⊆(M i).mode.val;rw [matchRow.1]
      change _≤ if assigned h M s.val i u.1=u.2.1 then (if (row h (M i) u.1).center=x ∧ s.val⊆(row h (M i) u.1).mode.val then
        Poly.toll w (row h (M i) u.1).mode*WilsonOriginalSuspendedTensor.paid (row h (M i) u.1) s.val t j r u.2.2 (σ/2) else 0) else 0
      simp only [W,m,if_pos matchRow,if_pos matchRow.2.2,if_pos (And.intro matchRow.2.1 sub),WilsonOriginalSuspendedTensor.paid]
      change _≤Poly.toll w (M i).mode*_
      rw [matchRow.1,←mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (reaches h M s x u i matchRow)) (half_pos hs).le)) non) (norm_nonneg _)
    · simpa only [m,if_neg matchRow,norm_zero,mul_zero] using wide.1 (E ⟨i,u⟩)
  apply WilsonOriginalFiniteSignedWage.original W priced m out paid
  have nn (y:Σ _:ι,Choice s.val n N G r):0≤W y.2*‖m y.1 y.2‖:=mul_nonneg (priced y.2) (norm_nonneg _)
  have limit (S:Finset (Σ _:ι,Choice s.val n N G r)):(∑y∈S,W y.2*‖m y.1 y.2‖) ≤ fee G σ r*C:=calc
    _ ≤ ∑y∈S,a (E y):=sum_le_sum (fun y _=>one y)
    _ = ∑z∈S.map E,a z:= (sum_map S E a).symm
    _ ≤ _:=(wide.2.1.sum_le_tsum (S.map E) (fun y _=>wide.1 y)).trans wide.2.2
  have summable:=summable_of_sum_le nn limit
  exact ⟨nn,summable,summable.tsum_le_of_sum_le limit⟩

end YM.Integration.WilsonOriginalRelativeMixedFields
