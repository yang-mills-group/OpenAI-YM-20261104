import YM.Integration.WilsonReceivedReplantedVerseTrail

/-! The actual cover conditional and the native scalar reversion use only the
purchased incoming coupling degrees, including the complete degree zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCoverGrade
open WilsonCoeffUV
open Filter Function Matrix Lattice RG Laurent Bloch Metric Wilson Tree
open AnalyticNext.QuarticMatch.Sheets Exterior Next.Free Precision
open WilsonCoeffUV WilsonCoeffUV.Blue FreeResolvent Work.F08
open WilsonCoeffUV.Bank WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Embroider
open WilsonCoeffUV.Embroider.Canvas Source Source.Drops Labels
open scoped Topology BigOperators Matrix.Norms.Frobenius

def Through {Y:Type*}(e:ℕ)(p q:ℕ→Y):Prop:=∀i,i≤e → p i=q i

variable {V α:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]
theorem heat [Fintype α](A:ropes Cover α α)(K:Layers ℝ (Cloth α)){P Q:ℕ→Gen V (Cloth α)}
    {e:ℕ}(same:Through e P Q)(n:ℕ):Through e (heap A K P n) (heap A K Q n):=by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i hi
    cases n with
    | zero => simpa only [level] using same i hi
    | succ n =>
      have paint (a:ropes Cover α α):paintC a K (heap A K P) n i=paintC a K (heap A K Q) n i:=by
        unfold paintC
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro l hl
        have sum₁:=Finset.HasAntidiagonal.mem_antidiagonal.mp hj
        have sum₂:=Finset.HasAntidiagonal.mem_antidiagonal.mp hl
        rw [ih j.2 (by omega) l.2 (by omega)]
      rw [inchC,inchC,ih n (by omega) i hi,paint,paint]

theorem reset {U:Type*}(c:Cost){P Q:Pal V U}{e:ℕ}(same:Through e P Q):
    Through e (Blue.mix c P) (Blue.mix c Q):=by
  intro i hi
  funext r
  unfold Blue.mix
  apply Finset.sum_congr rfl
  intro j hj
  rw [same j (by have w:=Finset.mem_range.mp hj;omega)]

variable {G:Gauge}
theorem joined (p:Patch)(K:KernelChoices)(a:ChartRatio G)
    (Γ:ropes Cover (Larvae G p.L) (Larvae G p.L))(M:ropes Cover (Larvae G p.L) (Hooks G))(W:Canvas G)
    (k:ℕ){P Q:Bookend V G}{e:ℕ}(same:Through e P Q):
    Through e (windsT p K a Γ M W k P) (windsT p K a Γ M W k Q):=by
  have chart:Through e (slidesJ p M P) (slidesJ p M Q):=by
    intro i hi
    unfold slidesJ
    rw [same i hi]
  intro i hi
  unfold windsT
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  exact heat _ _ chart n i hi

def Same (e:ℕ)(P Q:Era G V):Prop:=Through e P.2 Q.2

theorem verse (A:Levels G)(θ:ChartRatio G)(m N k:ℕ){P Q:Era G V}{e:ℕ}(same:Same e P Q):
    Same e (verseI A θ m N k P) (verseI A θ m N k Q):=
  reset _ (joined _ _ _ _ _ _ _ same)

end YM.Integration.WilsonReceivedCoverGrade
