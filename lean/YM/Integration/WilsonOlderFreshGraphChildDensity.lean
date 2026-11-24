import YM.Integration.WilsonOlderFreshGraphFinePreimages
import YM.Extra.SOURCE_HISTORIES.Pencil

/-! Reassemble the signed child comparisons on their common receiving root.
Regular labels keep their full component supports. Forced rows add at each
actual old key before the single common hard divisor. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphChildDensity
open Function Filter Finset Lattice Wilson RG Source Labels Extra.Histories
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:Side}{d:ℕ}{X:Type*}[Fintype X][Nonempty X]
variable {F:Frame G d}{o:Site n}{B:Hol G}{P:Rep G n}
variable {κ σ c Λ δ w:ℝ} {S:SectionData F}

def collected (h:X → ℂ) (A:X → Coefficient F n):Coefficient F n:=
  Extra.Histories.merge (Extra.Histories.code X) (fun x=>Extra.Histories.stretch (h x) (A x))

theorem represented (law:P.Lawful σ c Λ δ w)(pos:0<κ)
    (h:X → ℂ)(A:X → Coefficient F n)(b:X → ℝ)
    (F₀:∀x,(A x).Format o B P) (paid:∀x,(A x).remBound o P κ (b x))
    (push filed:X → Config G n → ℂ)
    (read:∀x U,(A x).density o S P U=push x U-(P.eval U:ℂ)*filed x U):
    let Q:=collected h A
    Q.Format o B P ∧ Q.remBound o P κ (∑x,‖h x‖*b x) ∧
      Q.x=∑x,h x • (A x).x ∧
      F.coeffSize Q.x ≤ ∑x,‖h x‖*F.coeffSize (A x).x ∧
      ∀U,Q.density o S P U= (∑x,h x*push x U)-(P.eval U:ℂ)*(∑x,h x*filed x U):=by
  intro Q
  let V(x:X):=Extra.Histories.stretch (h x) (A x)
  have fare(x:X):=(Extra.Histories.stretch_rem (h x) (paid x))
  have gross:Q.x=∑x,h x • (A x).x:=by simp only [Q,collected,Extra.Histories.merge,Extra.Histories.stretch,tsum_fintype]
  refine ⟨Extra.Histories.merge_format (Extra.Histories.code X) V (fun x=>Extra.Histories.stretch_format (h x) (F₀ x)),?_,gross,?_,?_⟩
  · have hb:=(Extra.Histories.merge_budget (Extra.Histories.code X) V pos fare (hasSum_fintype _).summable).1
    simpa only [Q,collected,V,tsum_fintype] using hb
  · rw [gross]
    simpa only [Extra.Histories.Size.smul] using (Extra.Histories.Size.finite F Finset.univ (fun x=>h x • (A x).x))
  intro U
  have pointwise:Q.density o S P U=∑x,(V x).density o S P U:=by
    have hx:=(Extra.Histories.merge_density (Extra.Histories.code X) V pos law fare (hasSum_fintype _).summable
      (hasSum_fintype _).summable S U).tsum_eq.symm
    simpa only [Q,collected,V,tsum_fintype] using hx
  rw [pointwise,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl;intro x _
  rw [show (V x).density o S P U = h x*(A x).density o S P U from Extra.Histories.stretch_density ..,read]
  ring

theorem funded (law:P.Lawful σ c Λ δ w)(pos:0<κ)
    (h:X → ℂ)(amp:X → ℝ)(awake:∀x,0<amp x)(fee:ℝ)
    (push filed:X → Config G n → ℂ)
    (sheets:∀x,∃(A:Coefficient F n)(b:ℝ), A.Format o B P ∧ A.remBound o P κ b ∧
      (∀U,A.density o S P U=push x U-(P.eval U:ℂ)*filed x U) ∧ amp x*(b+F.coeffSize A.x) ≤ fee):
    ∃(A:Coefficient F n)(b:ℝ), A.Format o B P ∧ A.remBound o P κ b ∧
      (∀U,A.density o S P U=(∑x,h x*push x U)-(P.eval U:ℂ)*(∑x,h x*filed x U)) ∧
      b+F.coeffSize A.x ≤ fee*(∑x,‖h x‖*(amp x)⁻¹):=by
  choose A b format priced row bill using sheets
  obtain ⟨frm,rem,_,primary,density⟩:=represented law pos h A b format priced push filed row
  refine ⟨collected h A,∑x,‖h x‖*b x,frm,rem,density,?_⟩
  have issued (x:X):b x+F.coeffSize (A x).x ≤ fee*(amp x)⁻¹:=by
    simpa only [div_eq_mul_inv] using ((le_div_iff₀ (awake x)).2 (by simpa only [mul_comm] using bill x))
  calc
    _ ≤ (∑x,‖h x‖*b x)+∑x,‖h x‖*F.coeffSize (A x).x:=add_le_add_right primary _
    _ = ∑x,‖h x‖*(b x+F.coeffSize (A x).x):=by simp only [mul_add,Finset.sum_add_distrib]
    _ ≤ ∑x,‖h x‖*(fee*(amp x)⁻¹):=Finset.sum_le_sum fun x _=>mul_le_mul_of_nonneg_left (issued x) (norm_nonneg _)
    _ = _:=by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro x _;ring
end YM.Integration.WilsonOlderFreshGraphChildDensity
end
