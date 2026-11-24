import YM.QCDVacuum.Stall.Hectares
/-!
# Vector spectators in an angular gauge regulator.
Elements of a REAL algebra; not commuting away the Grassmann signs.
Do not include the pin gauge average or unconstrained trees in separate diagrams.
-/
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
variable {τ : J ↪ Wing}
structure Carat (J I: Type)(S : StepData c f)(R : Rep G f)(τ:J↪Wing)(X : Type) where
  address _i (_:I) : Blade S R
  tags i j : (address i j).turn=τ i
  scent : J→ I→ X
namespace Carat
variable (K: Carat J I S R τ X) (e:I)
def choir (a:J→I) : Quartet J S R τ:= ⟨fun i=> K.address i (a i),fun i=> K.tags i (a i)⟩
def jingles (i:J)(U: Config G f): X := ∑ j,(K.address i j).ingredient U • K.scent i j
def openB (A: Finset J) (U: Config G f) : X:= if R.activities.admissible R.p U (pinKeys S τ A) then Real.exp (R.exponent U) • ∏ i∈A,K.jingles i U else 0

def motif (A: Finset J)(b:J→I): X:= ∏ i∈A,K.scent i (b i)
omit [Fintype J] [CompleteSpace X] in
private lemma baths [CompleteSpace X] (A: Finset J)(a:J→ℝ)(f:J→ X) : ∏ i∈ A,a i • f i=(∏ i∈A,a i) • ∏ i∈A,f i:=by
   induction A using Finset.induction_on <;> simp_all [mul_smul]
   rw [smul_comm]
lemma rehearsed (D:R.activities.K=0)(A: Finset J)(U:Config G f): K.openB A U= ∑ b∈ Fields.field A e,((K.choir b).seat A).cicada U • K.motif A b :=by
   unfold openB; simp_rw [Quartet.crack (K.choir _) _ D]; split <;> rename_i h
   ·  unfold jingles; rw [Fields.produce A e]; rw [Finset.smul_sum]; apply sum_congr rfl; intro i hi; rw [baths, ← mul_smul]; rfl
   · simp_rw [zero_smul,Finset.sum_const_zero]
variable (T) (x:ℝ) (χ:Chi)(b₀: ℝ)
def income (W a:ℝ) (Ñ:ChartRatio G)(l:ℕ)(V:Config G c)(p:Molecule S): X:= ∑ j∈ Fields.field (tick τ p) e, ((K.choir j).seat (tick τ p)).lotus T x χ b₀ W a Ñ l V p • K.motif (tick τ p) j

lemma tonal (D:R.activities.K=0)(A:Finset J)(V:Config G c)(Z:Finset (Molecule S)) :
    (if joints T R m (radiusB x) Z ∧ permitsA x V Z ∧ A=Z.biUnion (tick τ) then
      ∏ j∈Z,K.income T e x χ b₀ W a Ñ m V j else 0)=∑ j∈Fields.field A e, ((K.choir j).seat A).blossom T x χ b₀ W a Ñ m V Z • K.motif A j:=by
  simp_rw [Quartet.anthology _ _ D]; split
  next h=>
    let g p (x':J→I):= ((K.choir x').seat (tick τ p)).lotus T x χ b₀ W a Ñ m V p
    have hd : (Z:Set (Molecule S)).PairwiseDisjoint (tick τ (S:=S)):=by
      intro i hi j hj he; refine Finset.disjoint_left.mpr (fun k hx hh=>?_); exact Finset.disjoint_left.mp (unweave h.1 hi hj he) (show (registry S τ) k∈id i from (ticking ..).1 hx) ((ticking ..).1 hh)
    unfold income; rw [Fields.harvest Z _ hd]; swap
    · intro i hi f g he
      apply congr_arg₂ (· • ·) _ (Finset.prod_congr rfl (fun j hj=> congr_arg _ (he j hj)))
      congr 1
      suffices hz : ((K.choir f).seat (tick τ i)).own=((K.choir g).seat (tick τ i)).own by
        generalize hi : (K.choir f).seat _=Q at *; generalize hx : (K.choir g).seat _=W at *; cases Q; cases W; congr -- test
      unfold Quartet.seat; dsimp only; rw [map_eq_image,map_eq_image]; apply Finset.image_congr; exact fun j hj=> (congr_arg (K.address j) (he j hj))
    rw [← h.2.2]; apply Finset.sum_congr rfl; intro c hu
    rw [baths]; apply congr_arg₂ (· • ·) rfl; unfold motif; rw [h.2.2,prod_biUnion hd]
  next h=> simp_rw [zero_smul,Finset.sum_const_zero]

variable (H:Cash W x μ L Q o C T R) (D:R.activities.K=0)
include H D
lemma summons (F:Forest S.ratio)(V:Config G c)(A: Finset J): HasSum (fun Z : Finset (Molecule S) => overhead (prism T x χ o.K V F) R Q.table • (if joints T R Q.halo (radiusB x) Z ∧ permitsA x V Z ∧ A=Z.biUnion (tick τ) then ∏ j∈Z,K.income T e x χ o.K W o.a Q.table Q.halo V j else 0)) (S.push R.beta (K.openB A) V):= by
  let M j:=(K.choir j).seat A; let s:=Fields.field A e; let g j (U:Config G f):=(M j).cicada U • K.motif A j; have hz U: K.openB A U=∑ j∈s,g j U:= K.rehearsed e D A U
  have hi: S.IsKernel R.beta G:=S.isKernel (funds_branch H.laws.intake.ready) _
  have hp j: Integrable (fun U=> S.density R.beta U V • g j U) (prior G f) := StepData.push_slice hi V _ (((M j|>.sells H.laws.intake.cap).1.integrable _).smul_const (K.motif A j))
  have hh : S.push R.beta (K.openB A) V=∑ j∈s,S.push R.beta (M j).cicada V • K.motif A j := by
     unfold StepData.push; simp_rw [hz,Finset.smul_sum]; rw [integral_finsetSum _ (fun i _=> hp i)]; apply sum_congr rfl; intro i hi
     unfold g; simp_rw [← smul_assoc]; exact integral_smul_const ..
  rw [hh]; simp_rw [K.tonal T e x χ o.K D, Finset.smul_sum, ← smul_assoc]; exact hasSum_sum (s:=s) (fun j _=> (((M j).summons T x χ H F V).smul_const (K.motif A j)))
end Carat
end YM.PhysicalNext.Repeat.Lotus
