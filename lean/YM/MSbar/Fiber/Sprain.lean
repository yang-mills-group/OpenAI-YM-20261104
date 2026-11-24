import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Tassel
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Curtail
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Kiln
import YM.MSbar.Fiber.Badged
import YM.Push.BETA_TRANSPORT.Score



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

-- values with marked parameter, still original projection. scalar λ applied unnormalized all branches and before path W. 
abbrev color (M:Fibre S R)(H:Cash W x μ L Q o C T R) (χ : Chi) (V : Config G c) (t : ℝ) (m:Molecule S):= H.spawn χ V m+t*M.lotus T x χ o.K W o.a Q.table Q.halo V m
variable (χ : Chi)
lemma sprouting (V:Config G c)(t:ℝ): H.TaggedW (color M H χ V t):=by
  intro i hi; by_cases hp: H.spawn χ V i=0
  swap
  · obtain ⟨hx,-,hq,-⟩:= H.resident χ V _ hp; exact ⟨hx,hq⟩
  unfold color at hi; rw [hp,zero_add] at hi; obtain ⟨h,-,-,-,-,ha⟩:= whitherF M H V (χ:=χ) (right_ne_zero_of_mul hi); exact ⟨h,ha⟩

private lemma one_mark {A : Type*} [DecidableEq A] (p:A→ℝ)(q:A→ℝ)(t:ℝ)(S : Finset A)(h:∀i∈ S,q i≠0→ ∀j∈S,j≠i→ q j=0) :
    (∏ i∈S,(p i+t*q i))=(∏ i∈S,p i)+t*∑ i∈ S,q i * ∏ j∈ S.erase i, p j :=by
  by_cases ht:∃ i∈ S,q i≠0
  · obtain ⟨i,hi,hq⟩:= ht
    rw [← mul_prod_erase _ _ hi, Finset.sum_eq_single i, show ∏ j∈ S, p j=p i * ∏j∈ S.erase i,p j from (mul_prod_erase S p hi).symm]
    · rw [show ∏ i∈ S.erase i,(p i+t*q i)=_ from (prod_congr (g:=p) rfl fun j hj=> by rw [h i hi hq j (mem_of_mem_erase hj) (ne_of_mem_erase hj),mul_zero,add_zero])]; ring
    · intro j hj hx; rw [h _ hi hq j hj hx,zero_mul]
    simp [hi]
  push Not at ht; rw [show (∑ i∈S,q i * ∏ j∈ S.erase i,p j)=0 from Finset.sum_eq_zero fun i hi=> by rw [ht i hi,zero_mul],mul_zero,add_zero]; exact prod_congr rfl fun i hi=>by rw [ht i hi,mul_zero,add_zero]
lemma sprained (V: Config G c) (t:ℝ)(Z:Finset (Molecule S)): H.festo V (color M H χ V t) Z=festival T x χ o.K Q.table V R W o.a Q.halo Z+t*M.blossom T x χ o.K W o.a Q.table Q.halo V Z:=by
  unfold Cash.festo festival Fibre.blossom; dsimp only; split_ifs with hx
  swap; · simp
  let f m:=M.lotus T x χ o.K W o.a Q.table Q.halo V m; have hh i (hi:i∈Z)(hm:f i≠0) j (hj:j∈Z)(he:j≠i):f j=0:=by by_contra h; apply Finset.disjoint_left.mp (Matter.unweave hx.1 hj hi he) (show M.turn.badge S∈id j from (whitherF M H V h).2.2.1) (show M.turn.badge S∈ id i from (whitherF M H V hm).2.2.1)
  exact one_mark (H.spawn χ V) f t Z hh
lemma tint (V:Config G c)(t:ℝ)(F:Forest S.ratio): HasSum (fun p=> overhead (prism T x χ o.K V F) R Q.table * H.festo V (color M H χ V t) p)
    (S.push R.beta R.eval V+t*S.push R.beta M.cicada V):=by
  have he:= (Greenbelt.organizes T x χ H V (prism T x χ o.K V F) rfl rfl); have hp := M.summons T x χ H F V
  simp_rw [sprained M H χ,mul_add,mul_left_comm (overhead _ _ _) t]; exact he.add (hp.mul_left t)

end Charity.Storm
end YM.PhysicalNext.Repeat.Daisy
