import YM.Integration.WilsonMaxwellThermometerWardFinite
import YM.Integration.WilsonThermometerInversionStation

/-! The finite original registered inversion pupil has a sharper first face.
Only the upper cubic charge survives, before either regulator limit, with
every earned lower field still evaluated at its own site. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerRegisteredOdd
open Function Finset Lattice Wilson RG Labels Next.Rank PhysicalNext.Repeat.Legato
open WilsonMaxwellThermometerWardFinite WilsonMaxwellThermometerWardRoster WilsonMaxwellThermometerWardSocket
open WilsonOriginalThermometerPalette PertExtension PertExtension.Orb XSpace.Rose
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G) {I T:Type}[Fintype I][DecidableEq I](d:I→ℕ)
variable (v:(j:I)→R.family.label (d j))(t:I→T→ℂ)(N per:ℕ)(o:I→Site (R.family.side N per))
  (x:T)(L:ℂ→L[ℝ]ℝ)
local notation "g" => Pert.Asymptotics.regulatorRun R.family N per N
private abbrev threshold (R:Run G)(N per:ℕ):=(R.family.path.rep N per N).p.threshold
local notation "τ" => threshold R N per

def input (e:I→ℕ):ℝ :=
  Orb.diag (restrictedO (marked R d v t N per o x ((g)^(∑j,e j) • L) e)) ((∑j,e j)+1)

theorem cubic (simple:G.Simple)(cap:∀j,d j≤6):
    WilsonThermometerInversionFaces.series R d o (g) (τ) v t x L 1 =
      ∑e∈(masks R d).filter (fun e=>∃j,e j=3),input R d v t N per o x L e:=by
  have ev:=even_iff_two_dvd.mpr (ActualOriginalFiniteCoefficients.side_admissible R N per).2
  rw [WilsonMaxwellThermometerWardFinite.original R d v t N per o x L 1 ev,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hi:∃j,e j=3
  · rw [if_pos hi]; rfl
  rw [if_neg hi]
  have sumEq:(∑j,e j)=(∑j,e j/2)+(∑j,e j/2):=by
    rw [←Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _=>?_
    have h:=permitted R d simple he j
    have hc:=cap j
    have hn:e j≠3:=fun h=>hi ⟨j,h⟩
    omega
  have odd:Odd ((∑j,e j)+1):=⟨∑j,e j/2,by omega⟩
  exact Orb.normalized_odd (Orb.traySpec G) ev _ odd

theorem quiet (simple:G.Simple)(cap:∀j,d j≤4):
    WilsonThermometerInversionFaces.series R d o (g) (τ) v t x L 1=0:=by
  rw [cubic R d v t N per o x L simple (fun j=>(cap j).trans (by decide))]
  apply Finset.sum_eq_zero
  intro e he
  obtain ⟨book,j,hj⟩:=Finset.mem_filter.mp he
  have bound:=(permitted R d simple book j).1
  have hc:=cap j
  omega

/-- Keep precisely the actual upper pole-three coordinates and every lower
numerical coordinate including its scalar. -/
theorem same (pin:I→Fin 3)(inj:Function.Injective pin)(grade:d=levels ∘ pin)
    (simple:G.Simple) (u:(j:I)→R.family.label (d j))
    (agree:∀j,if pin j=0 then
       screen (R.family.labels.level (d j)) 3 (v j)=screen (R.family.labels.level (d j)) 3 (u j)
       else v j=u j):
    WilsonThermometerInversionFaces.series R d o (g) (τ) v t x L 1 =
    WilsonThermometerInversionFaces.series R d o (g) (τ) u t x L 1:=by
  have dh (i:Fin 3):levels i≤6:=by fin_cases i <;> decide
  have dl (i:Fin 3)(h:i≠0):levels i≤4:=by fin_cases i <;> first |contradiction|decide
  have upper (j:I):d j≤6:=grade ▸ dh (pin j)
  rw [cubic R d v t N per o x L simple upper,cubic R d u t N per o x L simple upper]
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨book,k,hk⟩:=Finset.mem_filter.mp he
  have top:pin k=0:=by
    by_contra no
    have hc:d k≤4:=grade ▸ dl (pin k) no
    have bound:=(permitted R d simple book k).1
    omega
  unfold input
  congr 2
  funext U
  unfold marked
  apply congrArg _
  apply Finset.prod_congr rfl
  intro j _
  by_cases p:pin j=0
  · have eq:j=k:=inj (p.trans top.symm)
    have h:=agree j
    rw [if_pos p] at h
    rw [show e j=3 from eq ▸ hk,h]
  · have h:=agree j
    rw [if_neg p] at h
    rw [h]

end YM.Integration.WilsonMaxwellThermometerRegisteredOdd
end
