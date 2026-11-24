import YM.Integration.WilsonPointChildCoveredRead
noncomputable section
namespace YM.Integration.WilsonPointChildCoveredCut
open Filter Function Finset YM FormalBulk08 Lattice RG Laurent Next.Foundations PhysicalNext.Repeat.Legato
open Reef Flat Stationary Dawn Pose Kemp Palm Shore Mesa Wine Quire Roof Lotus Sierra Gorge Dove Rial Rift Lava
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep WilsonPointChildFiledPress
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped ContDiff BigOperators Topology Classical ENNReal
variable {G:Gauge}{d D:ℕ}


def outside {V:Type}{r:ℕ}(D:Reach V)(z:V)(B:ℝ)(T:Tile V r):Tile V r:=
  fun x=>if B  ≤  herb D z x then T x else 0

theorem cut {V:Type}{r:ℕ}{D:Reach V}{z:V}{s A:ℝ}{T:Tile V r}
    (b:ℝ)(width:0 ≤ s)(paid:Knoxville D s z T A):
    Knoxville D (s/2) z (outside D z b T) (A*Real.exp (-s*b/2)):=by
  let t:=Real.exp (-s*b/2)
  have tp:0<t:=Real.exp_pos _
  refine ⟨mul_nonneg paid.1 tp.le,?_⟩
  calc
    _  ≤  ∑' x:chain V r,ENNReal.ofReal t*(Gorge.shine s (wide D (Fin.cons z x))*‖T x‖ₑ):=by
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases h:b ≤ herb D z x
      · simp only [outside,if_pos h,←mul_assoc]
        apply mul_le_mul_left
        unfold Gorge.shine
        rw [←ENNReal.ofReal_mul tp.le,←Real.exp_add]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        change s/2*(herb D z x) ≤  -s*b/2+s*(herb D z x)
        nlinarith [mul_nonneg width (sub_nonneg.mpr h)]
      · simp [outside,h]
    _ = ENNReal.ofReal t*∑' x:chain V r,Gorge.shine s (wide D (Fin.cons z x))*‖T x‖ₑ:=ENNReal.tsum_mul_left
    _  ≤  ENNReal.ofReal t*ENNReal.ofReal A:=mul_le_mul_right paid.2 _
    _ = ENNReal.ofReal (A*Real.exp (-s*b/2)):=by rw [←ENNReal.ofReal_mul tp.le,mul_comm]

theorem original (R:Run G)(simple:G.Simple)(paid:WilsonPointChildFiledTest.Filed R)
    (a:G.ColorIndex)(depth:d<D)(o:Loc G 1)(E:ℕ){η:ℝ}(pos:0<η):
    ∀ᶠm:ℕ in atTop,∀N,m ≤ N  →  ∀v:Letter (R.family.labels.level d),∀e ≤ E,∀r,∀p:Scroll D,∀b:ℝ,
    let z:edgeL G:=(0,o)
    let w:=width R m
    let T:=WilsonPointChildCoverReturn.table R a depth N (N-m) m v p e r
    Knoxville (fame _) (w/2) z (outside (fame _) z b T)
      (((R.family.path.levels.clock.hatBeta m)^η*‖physical p‖)*Real.exp (-w*b/2)):=by
  filter_upwards [WilsonPointChildCoveredRead.original R simple paid a depth o E pos] with m heard
  intro N live v e he r p b
  exact cut b ((Primer.FamilyWindow R.family).pos _).le ((heard N live v e he r).1 p)

end YM.Integration.WilsonPointChildCoveredCut
end
