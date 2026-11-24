import YM.QCDVacuum.Stall.Bead
/-! # Actual integral on vector labels, with optional exclusions. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable {J I : Type} [Fintype J] [Fintype I] {X : Type} [NormedCommRing X] [NormedAlgebra ℝ X] [CompleteSpace X]
variable {τ:J↪Wing}
-- fns of ONE V; its coarse uses factored later.
def gravy (τ : J↪Wing)(z:J→ Config G f→ X) (p:Molecule S)(X':Coat T F)(R:Rep G f)(l: ℕ)(Ñ:ChartRatio G)(W a:ℝ) (H:F.Slice G×Air f G) :=
    let Y:= X'.wrapY H.1
    let u:=Y.liftA R.beta H.2
    let M:=p \ ((tick τ p).map (registry S τ))
    (Y.term R Ñ W a (own p) l H.2 M * ∏ i∈tick τ p,Y.enforce (2*a) u (Y.plaza (Matter.areas R T 0 Y.B ((registry S τ) i)))) • ∏ i∈tick τ p,z i (Y.input u)

def juice (A:Type*) [Fintype A](f:A→X): X := (Fintype.card A : ℝ)⁻¹ • ∑ a,f a

def battery (τ:J ↪ Wing)(z:J→ Config G f→X) (p:Molecule S) (R:Rep G f)(l:ℕ)(T:Tube G S)(x:ℝ)(χ:Chi)(K:ℝ)(Ñ:ChartRatio G)(W a:ℝ)(V:Config G c) : X:=
    juice (Greenbelt.Reserve S) fun F=>
      let X:=prism T x χ K V (allot F); let Y:=planted X p
      if standsIn X R l p then juice S.Choices fun t=> ∫ H, gravy τ z p (Y.taggedL t) R l Ñ W a H ∂(((allot F).order G).prod (Y.taggedL t).dice) else 0

namespace Carat
variable (K: Carat J I S R τ X) (e:I)
variable (l:ℕ)
omit [CompleteSpace X] in
lemma fondant [CompleteSpace X] (p:Molecule S)(X':Coat T F)(H:F.Slice G×Air f G): gravy τ K.jingles p X' R l Ñ W a H = ∑ j∈ Fields.field (tick τ p) e, ((K.choir j).seat (tick τ p)).into X' W a Ñ (Matter.own p) l p H • K.motif (tick τ p) j :=by
  let Y:=X'.wrapY H.1; let A:=tick τ p; let u:= Y.liftA R.beta H.2; let ξ (i:J):= Y.enforce (2*a) u (Y.plaza (Matter.areas R T 0 Y.B ((registry S τ) i)))
  unfold gravy jingles; dsimp only; rw [Fields.produce (tick τ p) e]; rw [Finset.smul_sum]
  apply sum_congr rfl; intro i hi; rw [show ∏ j∈A,(K.address j (i j)).ingredient (Y.input u) • K.scent j (i j)=(∏ j∈A, (K.address j (i j)).ingredient (Y.input u)) • ∏ j∈A,K.scent j (i j) from ?hb, ← mul_smul]; swap
  · unfold A; induction tick τ p using Finset.induction_on with
    | empty=> simp
    | insert t s ht hx=> simp [ht,hx,mul_smul]; rw [smul_comm]
  apply congr_arg (· • K.motif (tick τ p) i)
  unfold Faction.into Faction.premium; rw [Quartet.hei, if_pos]; swap
  · intro k hk; obtain ⟨j,hj,rfl⟩:= mem_map.mp hk; exact (ticking ..).1 hj
  rw [show ((K.choir i).seat (tick τ p)).paidU Y a u = (∏ j∈A,(K.address j (i j)).ingredient (Y.input u))*(∏ j∈A,ξ j) from ?_]; swap
  · unfold Faction.paidU Quartet.seat; dsimp only; rw [prod_map, ← prod_mul_distrib]; refine prod_congr rfl (fun j _=>?_); dsimp only [Embedding.coeFn_mk]; unfold choir Blade.paidU Blade.fond; simp only [K.tags]; rfl -- test
  unfold ξ A Y u; ring
variable (T) (x:ℝ) (χ:Chi)
omit [Fintype I] [Fintype J] [CompleteSpace X] in
private lemma sings [Fintype I] [Fintype J] [CompleteSpace X] (M:Type) [Fintype M] (A:Finset (J→I))(F:M→(J→I)→ℝ)(v: (J→I)→X) : juice M (fun i=> ∑ j∈A,F i j • v j)=∑ j∈A, likely (fun i => F i j) • v j:=by
   unfold juice likely; rw [Finset.sum_comm, Finset.smul_sum]; apply sum_congr rfl; intro i _; rw [← Finset.sum_smul, ← mul_smul]
variable (H:Cash W x μ L Q o C T R) (D:R.activities.K=0)
-- if statement can be moved out of forest conditioning
include H
lemma lounges (p:Molecule S)(V:Config G c): battery τ K.jingles p R Q.halo T x χ o.K Q.table W o.a V=K.income T e x χ o.K W o.a Q.table Q.halo V p := by
    unfold battery; let A:=tick τ p; let F j:=(K.choir j).seat A; let X' (Y:Greenbelt.Reserve S):= prism T x χ o.K V (allot Y)
    let Z:= Fields.field A e
    have hz (Y:Greenbelt.Reserve S)(hu:standsIn (X' Y) R Q.halo p)(v:S.Choices):
       let Y':=(planted (X' Y) p).taggedL v
       (∫ a, gravy τ K.jingles p Y' R Q.halo Q.table W o.a a ∂(((allot Y).order G).prod Y'.dice))=∑ j∈Z,(F j).tithe Y' (Matter.own p) W o.a Q.table Q.halo p • K.motif A j := by
       intro Y'; simp_rw [K.fondant e]; rw [integral_finsetSum]; swap
       · exact fun i _=> ((F i|>.tip Y' _ H rfl (planted_valid (X' Y) p) _).2.1).smul_const _
       exact Finset.sum_congr rfl fun i _=> integral_smul_const ..
    dsimp only; rw [show K.income ..=∑ i∈Z, likely (fun Y:Greenbelt.Reserve S=> (F i).bloom (X' Y) W o.a Q.table Q.halo p) • K.motif A i from rfl, ← sings]; apply congr_arg; funext i
    split
    next h=>
       
       have hh := hz i h; dsimp only [X'] at hh; simp_rw [hh]; rw [sings]; exact sum_congr rfl fun j _=> congr_arg₂ _ (if_pos h|>.symm) rfl
    next h=> unfold Faction.bloom; simp_rw [X',if_neg h]; simp
omit H
lemma nutritive (A:Finset J)(H:Cash W x μ L Q o C T R)(D:R.activities.K=0)(e:I): Integrable (K.openB A) (prior G f):= by
   simp_rw [funext (K.rehearsed e D A)]; exact integrable_finsetSum _ fun i _=> (((K.choir i).seat A|>.sells H.laws.intake.cap).1.integrable _).smul_const _
end Carat
end YM.PhysicalNext.Repeat.Lotus
