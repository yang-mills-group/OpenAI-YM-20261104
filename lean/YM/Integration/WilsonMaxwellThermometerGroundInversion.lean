import YM.PertExtension.SlotSlope
import YM.Integration.WilsonMaxwellThermometerGroundDiagonal

/-! Every actual finite inversion-law monomial in the three registered
    radial source polynomials has the Gaussian table used by the
    seven-face diagonal cancellation, with its common positive vacuum. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonMaxwellThermometerGroundInversion
open Lattice PertExtension Orb RG MeasureTheory Next.Rank.Normal Finset
open Wilson Gauge Precision Function Filter Set Metric Matrix Chart Series Series.Radial GaussianScore
open scoped BigOperators Classical
variable {G : Gauge} {n : Side}

def sampler {V : Type*} (ev : Even n.val) (read : V → Orb.Source G n) : Symmetric V where
  cov i j := ↑((saddle ev).wick (read i) (read j))
  symm i j := by
    apply congr_arg Complex.ofReal
    let S:=saddle (G:=G) ev
    change read j (S.inverse (read i)) = read i (S.inverse (read j))
    calc
      _ = S.P (S.inverse (read j)) (S.inverse (read i)) := by rw [S.applies]
      _ = S.P (S.inverse (read i)) (S.inverse (read j)) := S.turns ..
      _ = _ := by rw [S.applies]

private theorem empty (ev : Even n.val) : Orb.gaussian (G:=G) ev (fun _=>1) = 1 := by
  unfold Orb.gaussian GaussianScore.Law.average
  simp only [Pi.mul_apply,one_mul]
  apply div_self
  rw [← saddleLaw ev]
  exact (integral_exp_pos (Orb.ker_integrable (G:=G) ev)).ne'

theorem measured {V A : Type*} [Fintype A] [DecidableEq A] (ev : Even n.val)
    (read : V → Orb.Source G n) (tag : A → V) (s : Finset A) :
    (↑(Orb.gaussian ev (fun u=>∏i∈s,read (tag i) u)):ℂ) =
      blend (sampler ev read) 0 (glyphs tag s) := by
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with he|hs
    · subst s; simp only [Finset.prod_empty,glyphs,WilsonMaxwellThermometerGroundInversion.empty,Next.Rank.Normal.fresh,Complex.ofReal_one]
    obtain ⟨i,hi⟩:=hs
    rw [gaussian_recursion ev (fun j=>read (tag j)) s hi]
    conv_rhs => rw [← insert_erase hi, spring _ _ _ _ (notMem_erase _ _)]
    simp only [Pi.zero_apply,zero_mul,zero_add,Complex.ofReal_sum,Complex.ofReal_mul]
    refine sum_congr rfl fun j _=>?_
    rw [ih _ ((erase_subset _ _).trans_ssubset (erase_ssubset hi))]
    exact mul_comm _ _

abbrev Entry (G : Gauge) := Fin 3 × LatticePT.Atom G

def earned (ev : Even n.val) (sites : Fin 3 → Cover) : Symmetric (Entry G) :=
  sampler ev fun i=> LatticePT.Slope.leg (wrap n (sites i.1)) i.2

theorem cross (ev : Even n.val) (sites : Fin 3 → Cover) (a b : Entry G) :
    (earned ev sites).cov a b =
      ↑(LatticePT.echo n (sites b.1) (sites a.1) (LatticePT.atAddress b.2) (LatticePT.atAddress a.2)) := by
  apply congr_arg Complex.ofReal
  exact LatticePT.Slope.cov ev _ _ _ _

/-- The directions are the actual selected plaquettes and colors of the
    head, retaining its original independent addresses and the vacuum. -/
theorem original {A : Type*} [Fintype A] [DecidableEq A] (ev : Even n.val)
    (sites : Fin 3 → Cover) (tag : A → Entry G) (s : Finset A) :
    (↑(Orb.gaussian ev (fun u=>∏i∈s,LatticePT.Slope.leg (wrap n (sites (tag i).1)) (tag i).2 u)):ℂ) =
      blend (earned ev sites) 0 (glyphs tag s) := by
  unfold earned
  exact measured (G:=G) (n:=n) (V:=Entry G) (A:=A) ev
    (fun p : Entry G=>LatticePT.Slope.leg (wrap n (sites p.1)) p.2) tag s
end YM.Integration.WilsonMaxwellThermometerGroundInversion
