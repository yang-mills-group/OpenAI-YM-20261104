import YM.Integration.WilsonThermometerRegisteredGroundWords

/-! Combine the real and imaginary projections only after expanding the
whole ordinary face. The original numerical coefficients then multiply
one polynomial in the actual addressed Gaussian score variables. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredGroundInk
open Finset Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato PertExtension PertExtension.Orb
open Next.Rank.Normal WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds
open WilsonThermometerRegisteredGroundWords WilsonMaxwellThermometerGroundInversion
open scoped Classical BigOperators ContDiff Topology
variable {G:Gauge} (R:Run G) {V T:Type} [Fintype V] (d:V→ℕ)
  (place:V→Fin 3) (sites:Fin 3→Lattice.Cover) {n:Side}
variable (g τ:ℝ) (v:(j:V)→R.family.label (d j)) (t:V→T→ℂ) (x:T)
local notation "e" j:max b:max => WilsonThermometerDeclaredSeeds.entry R d j (b j)
local notation "amt" b:max => ∏j:V,t j x*scalar R d g τ v (e j b)
local notation "O" b:max L:max => WilsonThermometerInversionSockets.word R d univ b
  (fun j=>wrap n (sites (place j))) g τ v t x L
local notation "w" b:max => WilsonThermometerInversionSockets.charge R d univ b

def sheet (b:(j:V)→Choice R d j) : poly (WilsonMaxwellThermometerGroundInversion.Entry G) :=
  ∑a:Colors R d b,((amt b) * ↑(cash R d b a)) • glyphs (tag R d b place a) univ

private lemma parts (q:ℂ) (a:ℝ) (y:ℂ) :
    (↑(q.re*a):ℂ)*y+Complex.I*(↑(q.im*a):ℂ)*y = (q*↑a)*y := by
  push_cast
  calc _ = ((q.re:ℂ)+(q.im:ℂ)*Complex.I)*a*y := by ring
       _ = _ := by rw [Complex.re_add_im]

theorem issued (ev:Even n.val) (b:(j:V)→Choice R d j) :
    (↑(Orb.diag (restrictedO (O b Complex.reCLM)) (w b)):ℂ) +
      Complex.I * ↑(Orb.diag (restrictedO (O b Complex.imCLM)) (w b)) =
      blend (earned ev sites) 0 (sheet R d place g τ v t x b) := by
  have re:=WilsonThermometerRegisteredGroundWords.original R d b place sites g τ v t x Complex.reCLM ev
  have im:=WilsonThermometerRegisteredGroundWords.original R d b place sites g τ v t x Complex.imCLM ev
  rw [re,im,Finset.mul_sum,←Finset.sum_add_distrib]
  simp only [sheet,map_sum,map_smul,smul_eq_mul]
  refine sum_congr rfl (fun a _=>?_ )
  rw [←mul_assoc]
  exact parts (amt b) _ _

def deposited : poly (WilsonMaxwellThermometerGroundInversion.Entry G) :=
  ∑b:(j:V)→Choice R d j,sheet R d place g τ v t x b

theorem original (ev:Even n.val) :
    (↑(WilsonThermometerInversionFaces.series R d (fun j=>wrap n (sites (place j))) g τ v t x Complex.reCLM 0):ℂ) +
      Complex.I*↑(WilsonThermometerInversionFaces.series R d (fun j=>wrap n (sites (place j))) g τ v t x Complex.imCLM 0) =
    blend (earned ev sites) 0 (deposited R d place g τ v t x) := by
  simp only [WilsonThermometerInversionFaces.series,Nat.add_zero,Complex.ofReal_sum,Finset.mul_sum,
    ←Finset.sum_add_distrib,deposited,map_sum]
  exact sum_congr rfl (fun b _=>issued R d place sites g τ v t x ev b)

end YM.Integration.WilsonThermometerRegisteredGroundInk
