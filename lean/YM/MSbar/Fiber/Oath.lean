import YM.MSbar.Fiber.Seed

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters March
namespace Charity.Storm
variable (M:Fibre S R) (H:Cash W x μ L Q o C T R)
    {s Y A b B C' v d q u r:ℝ}{j n:ℕ}{χ:Chi} (N: Captain H j q d v Y A b r B C' n χ)


set_option quotPrecheck false
local notation "D" => jewelDebt (paper M) Q L x
local notation "V₀" => Real.exp (Q.mark L μ x)
local notation "s₀"=> M.lotus T x χ o.K W o.a Q.table Q.halo
variable {τ β e:ℝ}{j₀:ℕ}(h:M.turn=Wing.gasKey j₀) (hb:Bikes Q L μ x a e B j n)(hf:foam Q L)
include H h

omit H h in
private lemma either {a b c t:ℝ} (h: 0≤c)(hT: 0< t) (hh : ∀ x:ℝ,|x| *c≤t→0<a+x*b): |b| ≤ a*(c/t) := by
  rcases eq_or_lt_of_le h with hc|hc
  · rcases eq_or_ne b 0 with h|he
    · rw [h,abs_zero,← hc,zero_div,mul_zero]
    have ht:= hh (-a/b) (by rw [← hc,mul_zero]; exact hT.le); rw [div_mul_cancel₀ _ he,add_neg_cancel] at ht; linarith only [ht]
  have hp : 0<t/c:=div_pos hT hc
  have hx : |t/c| *c ≤ t:=by rw [abs_of_nonneg hp.le,div_mul_cancel₀ _ hc.ne']
  have hy : 0<a-(t/c)*|b|:=by
    cases le_total 0 b with
    | inl h => rw [abs_of_nonneg h]; have hk:= hh (-(t/c)) (by rw [abs_neg]; exact hx); rw [neg_mul,← sub_eq_add_neg] at hk; exact hk
    | inr h=> rw [abs_of_nonpos h, mul_neg,sub_neg_eq_add]; exact hh (t/c) hx
  have he:(t/c)*|b|≤a:=by linarith
  rw [← show (t/c)⁻¹ = c/t from by simp,← div_eq_mul_inv]; apply (le_div_iff₀ hp).2; rwa [mul_comm]
include N hb hf
lemma signed (V:Config G c)(hv: RG.flags (Pressure.temp x) V=∅) :
    |S.push R.beta M.cicada V| ≤ S.push R.beta R.eval V*(R.p.mass M.crest M.weight/ Q.goal L x / V₀):=by
    have hx (t:ℝ)(ht:|t| * D≤V₀) := at_storm M H N h hb hf V hv ht
    let d:=coverNumber R.p.B M.crest; have he : -Q.ε*(d:ℝ) ≤0:=mul_nonpos_of_nonpos_of_nonneg (by linarith only [Q.usable]) (Nat.cast_nonneg _)
    have hR:=hx 0 (by rw [abs_zero,zero_mul]; exact (Real.exp_pos _).le); rw [zero_mul,add_zero] at hR
    have hD:=either (t:=V₀) (dew (paper M) H|>.2.1) (Real.exp_pos _) hx
    exact le_trans hD (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (mul_le_of_le_one_right (mul_nonneg (Real.exp_pos _).le (M.profit)) (Real.exp_le_one_iff.mpr he)) (arable H).le) (Real.exp_pos _).le) hR.le)
end Charity.Storm
end YM.PhysicalNext.Repeat.Daisy
