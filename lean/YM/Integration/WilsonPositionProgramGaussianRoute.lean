import YM.Integration.WilsonPositionProgramGaussianDriver

/-! Successive finite substitutions inside one signed, normalized Gaussian logarithm. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramGaussianRoute
open Function Finset Marker Multi Primitives.GCC.Anchor Comparison.RG02.Cumulants
open Extra.Trajectories (connected)
open MeasureTheory Next.Rank Next.SectorChange.Gaussian
open scoped BigOperators Classical
variable {I V:Type} [DecidableEq V] [Fintype V] [DecidableEq I] [Fintype I] {R:Census V}
  (Q:Matrix I I ℝ)(hQ:Q.IsSymm)(m:I→ℂ)
  (p q:Hot R→Normal.poly I)(s:R.Mode)(anchor:I→ℝ)

def staged (book:List (Hot R)) (i:Hot R):Normal.poly I:=if i∈book then q i else p i

def anchored (i:Hot R)(delta:Normal.poly I):Normal.poly I:=
  if i.val=s then delta else delta-MvPolynomial.C (Cloud.paint anchor delta)

def tally : List (Hot R)→Normal.poly I
  | [] => 0
  | i::rest =>
      let old:=staged p q rest
      let delta:=q i-old i
      anchored s anchor i delta * WilsonPositionProgramGaussianDriver.hearing Q hQ m old s i+
        tally rest

omit [Fintype V] [DecidableEq I] [Fintype I] in
private theorem step (i:Hot R)(book:List (Hot R)):
    staged p q (i::book)=update (staged p q book) i (q i):=by
  funext a
  by_cases eq:a=i
  · simp [eq,staged]
  · simp [staged,eq,update_of_ne]

omit [DecidableEq I] [Fintype I] in
theorem through_book (book:List (Hot R)):
    (connected (Cloud.prescription Q hQ m (staged p q book))).part s -
      (connected (Cloud.prescription Q hQ m p)).part s =
        Cloud.wick Q hQ m (tally Q hQ m p q s anchor book):=by
  induction book with
  | nil =>
      have idle:staged p q []=p:=funext fun i=>by simp [staged]
      rw [idle,sub_self,tally,map_zero]
  | cons i tail ih =>
      let old:=staged p q tail
      let co:=WilsonPositionProgramGaussianDriver.hearing Q hQ m old s i
      let delta:=q i-old i
      let F:=Cloud.wick Q hQ m
      have same:old i+delta=q i:=by unfold delta;ring
      have edge:=WilsonPositionProgramGaussianDriver.changed Q hQ m old s i delta
      rw [same,←step p q i tail] at edge
      have priced:F (anchored s anchor i delta * co)=F (delta*co):=by
        by_cases whole:i.val=s
        · simp [anchored,whole]
        · have cent:F co=0:=WilsonPositionProgramGaussianDriver.mean_zero Q hQ m old s i whole
          rw [anchored,if_neg whole,sub_mul,map_sub,MvPolynomial.C_mul',map_smul,cent,smul_zero,sub_zero]
      change _ = F (anchored s anchor i delta*co+tally Q hQ m p q s anchor tail)
      rw [map_add,priced,←edge,←ih]
      ring

theorem integrated (h:Q.PosSemidef)(real:I→ℝ):
    (connected (Cloud.prescription Q hQ (Cloud.shift real) q)).part s -
      (connected (Cloud.prescription Q hQ (Cloud.shift real) p)).part s =
    ∫z,Cloud.paint (real+z) (tally Q hQ (Cloud.shift real) p q s anchor Finset.univ.toList) ∂cloud Q:=by
  have whole:staged p q Finset.univ.toList=q:=by funext i; simp [staged]
  have booked:=through_book Q hQ (Cloud.shift real) p q s anchor Finset.univ.toList
  rw [whole] at booked
  exact booked.trans (Cloud.paid Q hQ h real _).2.symm

end YM.Integration.WilsonPositionProgramGaussianRoute
end
