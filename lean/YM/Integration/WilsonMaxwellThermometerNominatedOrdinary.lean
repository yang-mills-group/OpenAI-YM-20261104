import YM.Integration.WilsonMaxwellThermometerNominatedWard
import YM.Integration.WilsonThermometerCenteredAlgebra

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedOrdinary
open Function Lattice Wilson RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open Marker PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonNeutralNominatedFiniteTable
open WilsonMaxwellThermometerNominatedAlgebra WilsonThermometerCenteredAlgebra
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) (A:Group R.family 6) (N p k:ℕ)
local notation "J" => Stock.census (Fin 3)
local notation "d!"=>WilsonOriginalThermometerPalette.levels


private def grade {D:Fin 3→ℕ} {S:Finset (Fin 3)} {n:Side} (test:Case D) (angle:Woods G n→ℝ)
    (g:ℝ) (q a:ℕ) (P:Parcelized (Pen D S) G n):ℝ:=
  ∑e∈Finset.range (q+1),g^e*∑j∈Finset.range (a+1),∑u:Fin j→Woods G n,
    (∏v,angle (u v))*(pPly test S P e j u)

private theorem grade_smul {D:Fin 3→ℕ} {S:Finset (Fin 3)} {n:Side} (test:Case D) (angle:Woods G n→ℝ)
    (g:ℝ) (q a:ℕ) (c:ℝ) (P:Parcelized (Pen D S) G n):
    grade test angle g q a (c • P)=c*grade test angle g q a P:=by
  unfold grade
  simp only [map_smul,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  ac_rfl

private theorem unit {D:Fin 3→ℕ} {n:Side} (test:Case D) (angle:Woods G n→ℝ) (g:ℝ) (q a:ℕ):
    grade test angle g q a ((puff D G).1 n)=1:=by
  unfold grade
  rw [pen_puff]
  simp [uband,WilsonCoeffUV.Blue.shine,PowerSeries.coeff_one]

def component (t:Finset (Fin 3)) (i:Fin 3):ℂ→ₗ[ℝ]ℝ:=
  if i∈t then Complex.imLm else Complex.reLm

variable (caps:Fin 3→ℕ) (ok:∀i,d! i<caps i) (o:Fin 3→Site (R.family.side N p))
    (test:Case caps) (angle:Woods G (R.family.side k p)→ℝ) (g:ℝ) (q a:ℕ)

def amount (h:Fin 3→ℝ) (s t:Finset (Fin 3)):ℝ:=by
  let markers:=top R A N p caps ok (fun i=>h i • component t i)
  let operated:=Gears R.family.path.levels R.metals.O d! d! N N k markers
  let ordinates:Fin 3→Lattice.Cover:=fun i=>Lattice.lift (o i)
  let row:=levelsO (operated ordinates) s
  exact grade test angle g q a (row.1 (R.family.side k p))



def table (h:Fin 3→ℝ):Poly J:=
  Poly.inject fun s=>∑t∈s.val.powerset,Complex.I^t.card*(amount R A N p k caps ok o test angle g q a h s.val t:ℂ)

local notation "Q(" h ")"=>table R A N p k caps ok o test angle g q a h

private theorem empty (h:Fin 3→ℝ) (t:Finset (Fin 3)):
    amount R A N p k caps ok o test angle g q a h ∅ t=1:=by
  have zero (M:family G caps): levelsO M ∅=puff caps G:=by rw [levelsO,dif_pos rfl]
  unfold amount
  dsimp only
  rw [zero]
  exact unit _ _ _ _ _

theorem quiet (h:Fin 3→ℝ):(Q(h)).part (J).quiet=1:=by
  unfold table
  simp only [Poly.inject,Poly.part,Census.quiet,Finset.powerset_empty,Finset.sum_singleton,
    Finset.card_empty,pow_zero,one_mul,empty,Complex.ofReal_one]

theorem charged (simple:G.Simple) (hk:k≤N) (h:Fin 3→ℝ) (s:(J).Mode):
    (Q(h)).part s=(pay h s.val:ℂ)*(Q(fun _=>1)).part s:=by
  have each (t:Finset (Fin 3)) :
      amount R A N p k caps ok o test angle g q a h s.val t=
        pay h s.val*amount R A N p k caps ok o test angle g q a (fun _=>1) s.val t:=by
    obtain ⟨_,changeLog⟩:=WilsonMaxwellThermometerNominatedPupils.fitted R A N p caps ok (component t) h simple hk
      (fun i=>Lattice.lift (o i)) s.val
    unfold amount
    simp only [one_smul]
    rw [changeLog]
    exact grade_smul _ _ _ _ _ _ _
  change (∑t∈s.val.powerset,Complex.I^t.card*(_ :ℂ))= (pay h s.val:ℂ)*∑t∈s.val.powerset,Complex.I^t.card*(_ :ℂ)
  simp_rw [each,Complex.ofReal_mul,Finset.mul_sum]
  ac_rfl
end YM.Integration.WilsonMaxwellThermometerNominatedOrdinary
