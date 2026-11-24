import YM.Integration.WilsonIndependentCollarOpticalTrial

/-! One initial absolute wage works for all derivative evaluations of the
registered compact basis and all chamber points, including moving ones. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarPointBill
open Function Finset Lattice Laurent Wilson RG Source Labels Tree Exterior
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil
open IndependentSourcePathFamily OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonOriginalStarSceneWords WilsonReceivedCanonicalVerseBasis WilsonReceivedCanonicalVerseRegister
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open private comet atom from YM.Integration.IndependentSourcePathFamily
open scoped Classical BigOperators
variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι]

theorem unit (D:ℕ)(v:Knob D)(p:Chamber):‖claim D v p‖≤1:=
  (claim D v p).opNorm_le_bound zero_le_one (fun f=>by simpa only [one_mul,claim_take] using registry f v p)

def atoms {r:ℕ}(P:RG.Atom G r)(w:ℝ):ℝ:=
  ∑i,‖P.coeff i‖*|(rayOne (current P (1:ℝ)) i).budget w|

theorem bare {r D:ℕ}(P:RG.Atom G r)(v:Knob D)(p:Chamber)(w:ℝ):
    |integerP (current P (claim D v p)) w|≤atoms P w:=by
  unfold integerP atoms
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul,abs_of_nonneg (norm_nonneg _)]
  change ‖P.coeff i • claim D v p‖*|(rayOne (current P (1:ℝ)) i).budget w| ≤ _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) (unit D v p)) (abs_nonneg _)

def shape (R:Run G)(k:ι→ℕ)(j:ι)(c:Choice R k j):=
  let i:=entry R k j c
  colour (raw R k i).leg (key R k i) 1 Complex.reCLM

def coin (R:Run G)(k:ι→ℕ)(e:ℕ)(w:ℝ)(j:ι)(c:Choice R k j):ℝ:=
  ∑l:Fin (k j+e+1),atoms (shape R k j c) w * |flour G (steep w) (rank R k (entry R k j c)) l.val|

omit [Fintype ι] [DecidableEq ι] in
theorem cheap (R:Run G)(k:ι→ℕ)(e:ℕ)(w:ℝ)(j:ι)(c:Choice R k j):0≤coin R k e w j c:=by
  unfold coin atoms
  exact sum_nonneg fun _ _=>mul_nonneg (sum_nonneg fun _ _=>mul_nonneg (norm_nonneg _) (abs_nonneg _)) (abs_nonneg _)

omit [Fintype ι] [DecidableEq ι] in
theorem seat (R:Run G)(D k:ι→ℕ)(κ:(j:ι)→Knob (D j))(pt:ι→Chamber)(e:ℕ)(w:ℝ)
    (q:(j:ι)→Choice R k j)(j:ι):
    IndependentSourcePathFamily.charge (offer R k κ pt q) k e w j () ≤ coin R k e w j (q j):=by
  unfold IndependentSourcePathFamily.charge coin
  apply Finset.sum_le_sum
  intro l _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (bare (shape R k j (q j)) (κ j) (pt j) w) (abs_nonneg _)

theorem original (R:Run G)(D k:ι→ℕ)(e:ℕ){w:ℝ}(positive:0<w):
    ∃B:ℝ,1≤B ∧ ∀(κ:(j:ι)→Knob (D j))(pt:ι→Chamber)(q:(j:ι)→Choice R k j),
      let Y:=start R k κ pt q
      Wellness k Y ∧ ∀y S,shingled y S Y e w B:=by
  let B:=1+∑i,∑c:Choice R k i,coin R k e (4*w) i c
  have one:1≤B:=by
    apply le_add_of_nonneg_right
    exact Finset.sum_nonneg fun (i:ι) _=>Finset.sum_nonneg (s:=univ) (fun (c:Choice R k i) _=>cheap R k e (4*w) i c)
  refine ⟨B,one,?_⟩
  intro κ pt q Y
  let X:=offer R k κ pt q
  have gradeX (i)(b:Unit):(X i b).rank≤k i+(X i b).head:=grade R k κ pt i (q i)
  have price:bill X k e (4*w)≤B:=by
    unfold bill
    simp only [Fintype.sum_unique,default]
    have spent:(∑i,IndependentSourcePathFamily.charge X k e (4*w) i ()) ≤ ∑i,∑c:Choice R k i,coin R k e (4*w) i c:=
      Finset.sum_le_sum fun i _=>(seat R D k κ pt e (4*w) q i).trans
        (Finset.single_le_sum (fun c _=>cheap R k e (4*w) i c) (Finset.mem_univ (q i)))
    exact spent.trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨(OriginalCoverReanchoring.deposited X gradeX).1,?_⟩
  intro y S a ha r
  have fromWord:=preblock X (k:=k) y univ e (w:=4*w) (by positivity) gradeX
  have row:=fromWord.2.2.2 S (Finset.subset_univ _) a ha r
  have scale:steep (4*w)=w:=by unfold steep;ring
  rw [scale] at row
  exact row.more (pow_le_pow_left₀ fromWord.1 price _)

end YM.Integration.WilsonIndependentCollarPointBill
end
