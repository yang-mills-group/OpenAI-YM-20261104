import YM.Integration.QLocalMarkedSpectator
import YM.Integration.WilsonPrescribedPacketTail
import YM.Integration.LocalComparisonUniformModelPrice
import YM.Integration.NativePaidPacketColors

/-! Cut the genuine positive Laurent rows of one issued marked bank. The
original spatial paths and compulsory spectator remain inside the read. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalLaurentOrderTail

open Finset Lattice Wilson RG Marker Comparison.Density.RenderM
open LocalComparison LocalComparison.MarkedPackets Push.AbsoluteSums
open scoped Classical BigOperators

variable {G:Gauge} {V:Type} [DecidableEq V] {D:V → ComparisonDensity.Address.Orbit} {Γ:Census V} {n:Side}
    (P:MarkedPackets D G n Γ) (p:ℕ) {q:BudgetPoint} {a:V→Support n}
    {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width budget:ℝ} {off cov:ℕ}

def lower:=WilsonPrescribedPacketTail.slice P (fun i=>P.power i≤(p:ℤ))
def upper:=WilsonPrescribedPacketTail.slice P (fun i=>(p:ℤ)<P.power i)

private theorem actual {i:ℕ} {T:Token G n (fun v=>(D v).Mood) (P.rank i)}
    (h:(upper P p).packet i=some T) : P.packet i=some T := by
  by_cases e:(p:ℤ)<P.power i
  · simpa only [upper,WilsonPrescribedPacketTail.slice,if_pos e] using h
  · simp only [upper,WilsonPrescribedPacketTail.slice,if_neg e,reduceCtorEq] at h

theorem paid (H:P.Paid q a region w 1 width budget off cov) (hg:0<g) (hs:g≤1) :
    (upper P p).Paid q a region w g width (g^(p+1)*budget) off cov := by
  refine {width_pos:=H.width_pos,positive:=H.positive,
          coefficient:=fun i T h=>H.coefficient i T (actual P p h),
          paths:=fun i T h=>H.paths i T (actual P p h),
          addresses:=fun i T h=>H.addresses i T (actual P p h),
          symmetry:=fun i T h=>H.symmetry i T (actual P p h),
          reads:=fun i T h=>H.reads i T (actual P p h),
          multilinear:=fun i T h=>H.multilinear i T (actual P p h),
          cover:=fun i T h=>H.cover i T (actual P p h),width_reserved:=H.width_reserved,roots:=?_}
  intro v
  apply budget_mono (budget_scale (pow_nonneg hg.le (p+1)) (H.roots v))
  · intro i
    by_cases hv:v∈(P.mode i).val <;> by_cases h:(p:ℤ)<P.power i <;>
      simp only [upper,WilsonPrescribedPacketTail.slice,hv,h,ite_true,ite_false,ite_self,le_refl]
    cases e:P.packet i with
    | none=>simp
    | some T=>
      have hw:0≤Poly.toll w (P.mode i):=(Poly.worth H.positive _).le
      have hc:= (H.coefficient i T e).1
      positivity
  · intro i
    by_cases hv:v∈(P.mode i).val
    · by_cases h:(p:ℤ)<P.power i
      · simp only [upper,WilsonPrescribedPacketTail.slice,hv,h,ite_true,
          Complex.ofReal_one,one_zpow,norm_one,mul_one]
        cases e:P.packet i with
        | none=>simp
        | some T=>
          have hz:‖(g:ℂ)^P.power i‖≤g^(p+1):=by
            rw [norm_zpow,Complex.norm_real,Real.norm_of_nonneg hg.le]
            calc
              _≤g^((p+1:ℕ):ℤ):=zpow_le_zpow_right_of_le_one₀ hg hs (by omega)
              _=g^(p+1):=zpow_natCast _ _
          have hw:0≤Poly.toll w (P.mode i):=(Poly.worth H.positive _).le
          have hc:= (H.coefficient i T e).1
          calc _≤(Poly.toll w (P.mode i)*g^(p+1)*T.coin)*Real.exp (width*T.fall):=
                 mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz hw) hc) (Real.exp_pos _).le
               _=_:=by ring
      · have z:=mul_nonneg (pow_nonneg hg.le (p+1)) ((H.roots v).1 i)
        simpa only [upper,WilsonPrescribedPacketTail.slice,hv,h,ite_true,ite_false] using z
    · simp [upper,WilsonPrescribedPacketTail.slice,hv]

variable [Fintype V]

theorem split (H:P.Paid q a region w 1 width budget off cov) (hg:0<g) (hs:g≤1)
    (x:TestSpace D) (U:Config G n) :
    (lower P p).read x g U=P.read x g U-(upper P p).read x g U := by
  have all:=NativePaidPacketColors.read_summable H one_ne_zero x g U
  have rest:=NativePaidPacketColors.read_summable (paid P p H hg hs) hg.ne' x g U
  unfold MarkedPackets.read
  rw [←all.tsum_sub rest]
  apply tsum_congr
  intro i
  by_cases h:P.power i≤(p:ℤ)
  · cases e:P.packet i <;> simp [lower,upper,WilsonPrescribedPacketTail.slice,MarkedPackets.term,e,h,not_lt.mpr h]
  · cases e:P.packet i <;> simp [lower,upper,WilsonPrescribedPacketTail.slice,MarkedPackets.term,e,h,lt_of_not_ge h]

theorem measured (H:P.Paid q a region w 1 width budget off cov) (hg:0<g) (hs:g≤1)
    (x:TestSpace D) (U:Config G n) (spectator:Poly Γ) :
    Poly.pass ((lower P p).read x g U)*spectator=
      Poly.pass (-(upper P p).read x g U)*(Poly.pass (P.read x g U)*spectator) := by
  apply QLocalMarkedSpectator.multiply
  · rw [split P p H hg hs]; abel
  · exact P.quiet_read _ _ _
  · rw [Poly.part_neg,(upper P p).quiet_read,neg_zero]

theorem charged (H:P.Paid q a region w 1 width budget off cov) (hg:0<g) (hs:g≤1)
    (cap:ℕ) (hc:P.rankCap≤cap) (t:IndependentTests D) (U:Config G n) (spectator:Poly Γ) :
    let δ:=uniformReadCost cap (Fintype.card V) (g^(p+1)*budget)
    let x:=testInclusion D t
    δ≤1 → Poly.price w (Poly.pass ((lower P p).read x g U)*spectator-Poly.pass (P.read x g U)*spectator)
      ≤2*δ*Poly.price w (Poly.pass (P.read x g U)*spectator) := by
  intro small
  apply QLocalMarkedSpectator.charge H.positive _ _ (-(upper P p).read (testInclusion D t) g U) _
  · rw [split P p H hg hs]; abel
  · exact P.quiet_read _ _ _
  · rw [Poly.part_neg,(upper P p).quiet_read,neg_zero]
  · have qread:=((paid P p H hg hs).uniform_read cap hc t U).2
    simpa only [Poly.price,Poly.part_neg,norm_neg] using qread

end YM.Integration.QLocalLaurentOrderTail
