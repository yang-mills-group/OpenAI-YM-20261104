import YM.Integration.WilsonThermometerWeakRetainedRow

/-! Support-by-support hearing of every distant occurrence of the actual displaced
coefficient. The receiving support tariff is paid before summing the original sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakLongOccurrences
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open Next.Rank Next.Rank.Edition Next.Rank.Spindle Configuration Rise
open Thirst Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Cells Atlas Baler EntryWord Exponential
open WilsonThermometerWeakTaylor WilsonThermometerWeakRetainedRow
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} {d:ℕ} {F:Frame G d} {n:Side} {P:Rep G n} {m:ℕ}

theorem funded (X:Coefficient F n) {κ cash y:ℝ} (income:X.remBound 0 P κ cash)
    (q:BudgetPoint) (low:Lower P.p q) (hy:0≤y) (rate:scalesExp P.p q (2*y)) :
    ∃ c:Far (P:=P) X m→ℝ,
      (∀ j,0≤c j ∧ ∀ U,Healthy P.p.threshold (X.support j) U→‖X.regular j U‖≤c j) ∧
      Summable c ∧ Summable (fun j=>c j*debt q.B y (halo 8 (X.support j))) ∧
      (∑' j,c j*debt q.B y (halo 8 (X.support j)))≤
        Real.exp (100000*y)*Real.exp (-(P.p.supportExponent*m)/2)*cash := by
  obtain ⟨a,b,_,hb,total,_,⟨ℓ,fee,rows⟩,_⟩:=income
  let c (j:Far (P:=P) X m):=ℓ j.val
  let Z (j:Far (P:=P) X m):=X.support j
  let f (j:Far (P:=P) X m):=P.p.mass (Z j) (c j)
  let A:=Real.exp (100000*y);let B:=Real.exp (-(P.p.supportExponent*m)/2)
  have c0 j:0≤c j:=(rows _).1
  have fin:Summable f:=fee.2.1.subtype _
  have cfin:Summable c:=fin.of_nonneg_of_le c0 (fun i=>P.p.loMass (Z i) (c i) (c0 i))
  have funded:(∑' j,f j)≤cash:=(fee.2.1.tsum_subtype_le _ _ fee.1).trans (fee.2.2.trans ((le_add_of_nonneg_right hb).trans total))
  let d1 j:=debt q.B y (halo 8 (Z j))
  have geom j:d1 j≤A*Real.exp (P.p.supportExponent*coverNumber P.p.B (Z j)/2):=by
    have h:=scaler P.p q low rate (show 0≤2*y by positivity) (Z j)
    change debt _ _ _≤_ at h;unfold debt at h
    rw [←Real.exp_add,Real.exp_le_exp] at h
    unfold A d1 debt;rw [←Real.exp_add];apply Real.exp_le_exp.mpr;linarith only [h]
  have spent j:c j*d1 j≤A*B*f j:=by
    apply (mul_le_mul_of_nonneg_left (geom j) (c0 j)).trans
    let v:ℝ:=coverNumber P.p.B (Z j)
    have hv:(m:ℝ)≤v:=by unfold v Z;exact_mod_cast Nat.le_of_lt (lt_of_not_ge j.property)
    have w:Real.exp (P.p.supportExponent*v/2)≤B*Real.exp (P.p.supportExponent*v):=by
      unfold B;rw [←Real.exp_add];apply Real.exp_le_exp.mpr
      linarith only [mul_le_mul_of_nonneg_left hv P.p.exponent_pos.le]
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left w (Real.exp_pos _).le) (c0 j)).trans_eq
    dsimp only [A,B,f,v,BudgetPoint.mass];ring
  have full:Summable (fun j=>A*B*f j):=fin.mul_left _
  have paid:Summable (fun j=>c j*d1 j):=full.of_nonneg_of_le (fun j=>mul_nonneg (c0 j) (Real.exp_pos _).le) spent
  refine ⟨c,fun j=>⟨c0 j,fun U h=>(rows j).2 U h [] (Nat.zero_le _) (by simp)⟩,cfin,paid,?_⟩
  refine (paid.tsum_le_tsum spent full).trans ?_
  rw [tsum_mul_left];exact mul_le_mul_of_nonneg_left funded (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)

variable {C:Family G} {N k p:ℕ} {V:Type} [Fintype V] [DecidableEq V]
local notation "ℙ" => C.path.rep N p k
def field (X:Coefficient (C.labels.level d) (C.side k p)) (N m:ℕ) (Z:Keepat (C.side k p)) (U:Config G (C.side k p)):ℂ:=
  ∑' j:Far (P:=C.path.rep N p k) X m,if X.support j=Z.val then X.regular j U else 0

private theorem localField (X:Coefficient (C.labels.level d) (C.side k p)) (form:X.Format 0 C.params ℙ)
    (Z:Keepat (C.side k p)) : Reliable 0 G _ Z.val (field X N m Z) := by
  constructor
  · intro g U;apply tsum_congr;intro i;rw [(form.smooth i).symmetry g U]
  · apply Measurable.tsum;intro i;split;exact (form.smooth i).borel;exact measurable_const
  intro U U' h;apply tsum_congr;intro i;split
  · rename_i hi;exact (form.smooth i).sites _ _ (hi.symm ▸ h)
  rfl

def filed (X:Coefficient (C.labels.level d) (C.side k p)) (form:X.Format 0 C.params ℙ)
    (m:ℕ) {ζ:V→Site (C.side k p)} (s:Signed) (r:Prop) (x:V) (Z:Keepat (C.side k p)):SourceAt G ζ:=
  Edition.traverse (C:=C) s r x Z.property (localField (m:=m) X form Z)

theorem priced (X:Coefficient (C.labels.level d) (C.side k p)) (form:X.Format 0 C.params ℙ)
    {κ cash y:ℝ} (input:X.remBound 0 ℙ κ cash) (q:BudgetPoint) (low:Lower (ℙ).p q)
    (hy:0≤y) (rate:scalesExp (ℙ).p q (2*y)) {ζ:V→Site (C.side k p)}
    (s:Signed) (r:Prop) (x:V) (w:V→ℝ) (hw:0≤w x) :
    let E:=filed (m:=m) X form (ζ:=ζ) s r x
    ∃ c:Keepat (C.side k p)→ℝ, (∀ j,transported (E j) (ℙ).p.threshold w (c j)) ∧
      (∑ j,c j*debt q.B y (halo 8 (E j).extent))≤
        Real.exp (100000*y)*Real.exp (-((ℙ).p.supportExponent*m)/2)*(w x*cash) := by
  intro E
  obtain ⟨ℓ,rows,fin,payFin,spent⟩:=funded (m:=m) X input q low hy rate
  let K (i:Far (P:=ℙ) X m):Keepat (C.side k p):=⟨X.support i,form.origin i⟩
  let c (a:Keepat (C.side k p)):=∑' i,pay ℓ (fun i=>K i=a) i
  have pos a:0≤c a:=tsum_nonneg fun i=>by unfold pay;split;exact (rows i).1;exact le_rfl
  have capped a U (ha:Healthy (ℙ).p.threshold a.val U):‖field X N m a U‖≤c a:=by
    let S (i:Far (P:=ℙ) X m):=if X.support i=a.val then X.regular i U else 0
    let W (i:Far (P:=ℙ) X m):=pay ℓ (fun i=>K i=a) i
    have leS i:‖S i‖≤W i:=by
      unfold S W pay;by_cases same:X.support i=a.val
      · rw [if_pos same,if_pos (Subtype.ext same)];exact (rows i).2 U (same.symm ▸ ha)
      rw [if_neg same,norm_zero,if_neg (fun e=>same (congrArg Subtype.val e))]
    have fW:Summable W:=fin.indicator (s:={i|K i=a})
    have fS:=fW.of_nonneg_of_le (fun i=>norm_nonneg (S i)) leS
    exact (norm_tsum_le_tsum_norm fS).trans (fS.tsum_le_tsum leS fW)
  refine ⟨fun a=>w x*c a,fun a=>(transferD ..).2 ⟨mul_nonneg hw (pos a),fun U h=>?_⟩,?_⟩
  · change Poly.toll w (slot x)*‖dot r _‖≤_
    rw [Poly.solo_toll,dot_norm];exact mul_le_mul_of_nonneg_left (capped a _ ((s_healthy s (ζ x) ..).2 h)) hw
  let t (i:Far (P:=ℙ) X m):=ℓ i*debt q.B y (halo 8 (X.support i))
  have sum a:c a*debt q.B y (halo 8 (E a).extent) = ∑' i,pay t (fun i=>K i=a) i:=by
    change c a*debt q.B y (halo 8 (swath s (ζ x) a.val))=_
    rw [←swath_iffHalo,debt,swath_cover];unfold c;rw [←tsum_mul_right];apply tsum_congr;intro i
    unfold pay;split_ifs with h;rw [←h];rfl
    rw [zero_mul]
  simp_rw [mul_assoc (w x),sum];rw [←Finset.mul_sum,pack_all _ K payFin]
  exact (mul_le_mul_of_nonneg_left spent hw).trans_eq (mul_left_comm ..)

end YM.Integration.WilsonThermometerWeakLongOccurrences
end
