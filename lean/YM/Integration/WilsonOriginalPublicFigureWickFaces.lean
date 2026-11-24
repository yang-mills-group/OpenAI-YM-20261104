import YM.Integration.WilsonOriginalPublicFigureWick

/-! The three registered raw coefficients are folded on their one original
finite tree. The position insertions carry their own restored engineering
weights, with both finite changes retained on all the original peers. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 500000
namespace YM.Integration.WilsonOriginalPublicFigureWickFaces
open Function Finset Lattice Wilson RG Labels PhysicalNext.Repeat.Legato PowerSeries
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell Maxwell.Wick
open WilsonOriginalPublicFigureWick (project remainder superior)
open WilsonMaxwellThermometerPositionCurrency (received physicalWord)
open WilsonThermometerPositionTunedSlope (Columns paid price finite)
open WilsonThermometerPositionTunedCorrection (surveyed residual)
open WilsonPositionProgramTrialThermalGrades (frozen)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G){n:ℕ}(h:Fin n→ℕ)
    (v:(i:Fin n)→(R.family.labels.level (h i)).Coeff)(X:Sample n)(S:Finset (Fin n))
local notation "F" i:max => R.family.labels.level (h i)
local notation "T" => W.tree X.F.p
local notation "hS" => (h ∘ Subtype.val:S→ℕ)
local notation "vS" => (fun i:S=>v i)
local notation "zS" => (fun i:S=>X.layout i)

theorem letters (i:Fin n):
    Bare.raw T (W.surveys (h i)) (chartV X i) ((F i).coords.symm (v i)).val=
      ∑b:(F i).Index,v i b •
        WilsonThermometerPositionTunedSurvey.row R W (h i) X.F.p T (chartV X i) b:=by
  let L:=Bare.column T (W.surveys (h i)) (chartV X i) ∘ₗ
    (W.surveys (h i)).insertW 1
  have leg(y:Label G (h i)):L y=Bare.raw T (W.surveys (h i)) (chartV X i) y.val:=by
    change Bare.column T (W.surveys (h i)) (chartV X i) ((W.surveys (h i)).insertW 1 y)=_
    rw [Bare.column_formula,(W.surveys (h i)).wick_recovers]
  rw [←leg,← (F i).basis.sum_repr ((F i).coords.symm (v i)),map_sum]
  apply sum_congr rfl
  intro b _
  rw [map_smul,leg]
  have eq:(F i).basis.repr ((F i).coords.symm (v i)) b=v i b:=
    congrFun ((F i).coords.apply_symm_apply (v i)) b
  rw [eq]
  rfl

theorem folded:
    paid R hS (frozen R hS vS) (surveyed R W hS X.F.p zS T)=
      Bare.normalized T G (∏i∈S,Bare.raw T (W.surveys (h i)) (chartV X i)
        ((F i).coords.symm (v i)).val):=by
  rw [←prod_coe_sort S]
  simp_rw [letters R W h v X,Fintype.prod_sum]
  rw [map_sum,paid]
  apply sum_congr rfl
  intro b _
  have weight:price R hS (frozen R hS vS) b=PowerSeries.C (∏i:S,v i (b i)):=
    (map_prod PowerSeries.C _ univ).symm
  rw [weight,←PowerSeries.smul_eq_C_mul]
  rw [show (∏i:S,v i (b i) • WilsonThermometerPositionTunedSurvey.row R W (h i) X.F.p T (chartV X i) (b i))=
    (∏i:S,v i (b i)) • ∏i:S,WilsonThermometerPositionTunedSurvey.row R W (h i) X.F.p T (chartV X i) (b i) by
      simp only [Algebra.smul_def,Finset.prod_mul_distrib,map_prod],map_smul]
  rfl

def ordinary (K:ℕ)(i:Fin n):Bare.Series T G:=
  regal W (h i) X (chartV X i) (received X (R.family.S.a K)
    ((R.family.S.a K:ℂ)^(h i) • project W (F i) (v i)))

def surplus (i:Fin n):Bare.Series T G:=
  superior W (F i) X (chartV X i) (v i)+
  Bare.column T (W.surveys (h i)) (chartV X i) (remainder W (F i) (v i))

theorem original (K:ℕ):
    paid R hS (frozen R hS vS) (finite R hS X.F.p zS T) -
      Bare.normalized T G (∏i∈S,ordinary R W h v X K i)=
      paid R hS (frozen R hS vS) (WilsonThermometerPositionTunedCorrection.residual R W hS X.F.p zS T)+
      Bare.normalized T G ((∏i∈S,(ordinary R W h v X K i+surplus R W h v X i))-
        ∏i∈S,ordinary R W h v X K i):=by
  have same:=WilsonThermometerPositionTunedCorrection.earned R W hS X.F.p zS T (frozen R hS vS)
  rw [folded R W h v X S] at same
  have single (i:Fin n):Bare.raw T (W.surveys (h i)) (chartV X i) ((F i).coords.symm (v i)).val=
      ordinary R W h v X K i+surplus R W h v X i:=by
    simpa only [ordinary,surplus,add_assoc] using
      WilsonOriginalPublicFigureWick.priced_word W (F i) X (R.family.S.a K) (R.family.S.a_pos K).ne'
        (chartV X i) (v i)
  simp_rw [single] at same
  rw [←same,map_sub]
  abel

end YM.Integration.WilsonOriginalPublicFigureWickFaces
end
