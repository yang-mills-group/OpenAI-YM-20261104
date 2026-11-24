import YM.QCDVacuum.Stall.Bauble
/-!
# Gauge shell output, with inclusion rule for spectator dictionary

K plane vacuum on auxiliary ledger **turned off**. No constraints against
log/gauge labels. K-on uses specialized summability and has different readout.
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
variable {τ:J↪Wing} (d:J→J→Prop)

def agreesD (A: Finset J) := (A:Set J).Pairwise d

lemma connection (τ : J↪Wing) (Z:Finset (Molecule S)) (h:joints T R m (radiusB x) Z) (p:∀ i j,i≠j→Disjoint (Matter.areas R T m (radiusB x) (registry S τ i)) (Matter.areas R T m (radiusB x) (registry S τ j)) → d i j) : agreesD d (Z.biUnion (tick τ)) ↔ ∀ i∈ Z, agreesD d (tick τ i) :=by
   constructor
   · intro hz i hi; exact fun j hj k hk hn=> hz (Finset.mem_biUnion.mpr ⟨i,hi,hj⟩) (mem_biUnion.mpr ⟨i,hi,hk⟩) hn
   intro hh i hi j hj hf; obtain ⟨k,hk,ht⟩:= mem_biUnion.mp hi; obtain ⟨l,hl,hy⟩:= mem_biUnion.mp hj
   by_cases hp:k=l
   · exact hh l hl (hp ▸ ht) hy hf
   exact p i j hf ((h.2 hk hl hp).mono (subset_biUnion_of_mem _ ((ticking ..).1 ht)) (subset_biUnion_of_mem _ ((ticking ..).1 hy)))

def prance (τ : J↪Wing) (R:Rep G f) (p:Molecule S)(l:ℕ)(T:Tube G S)(x:ℝ)(χ:Chi)(K:ℝ)(Ñ:ChartRatio G)(W a:ℝ)(V:Config G c) (v:J→ Config G f→X) : X:= if agreesD d (tick τ p) then battery τ v p R l T x χ K Ñ W a V else 0
namespace Carat
variable (K: Carat J I S R τ X) (e:I)
def printD (U:Config G f): X:= ∑ i ∈ (univ.filter (agreesD d)), K.openB i U
variable (T) (x:ℝ) (χ:Chi)
variable (H:Cash W x μ L Q o C T R) (D:R.activities.K=0)
variable (h:∀ i j,i≠j → Disjoint (H.supportP (registry S τ i)) (H.supportP (registry S τ j)) → d i j)
include H h D e
omit D h in
lemma recued (_D:R.activities.K=0) (h:∀ i j,i≠j → Disjoint (H.supportP (registry S τ i)) (H.supportP (registry S τ j)) → d i j) (Z:Finset (Molecule S))(V:Config G c) :
    (if joints T R Q.halo (radiusB x) Z ∧ permitsA x V Z then ∏ j∈Z, prance d τ R j Q.halo T x χ o.K Q.table W o.a V K.jingles else 0) =
    ∑ A∈ univ.filter (agreesD d), (if joints T R Q.halo (radiusB x) Z ∧ permitsA x V Z ∧ A=Z.biUnion (tick τ) then ∏ j∈Z,K.income T e x χ o.K W o.a Q.table Q.halo V j else 0) :=by
  split
  next hp=>
    let P:=Z.biUnion (tick τ)
    have he(A : Finset J) : (joints T R Q.halo (radiusB x) Z ∧ permitsA x V Z ∧ A=P)↔ P=A := by rw [and_iff_right hp.1,and_iff_right hp.2,eq_comm]
    unfold P at he; simp_rw [he]; rw [sum_ite_eq]
    by_cases hm : agreesD d P
    · rw [if_pos (mem_filter.mpr ⟨mem_univ _,hm⟩)]; refine prod_congr rfl (fun i hi=>?_); unfold prance; rw [if_pos ((connection (x:=x) d τ Z hp.1 h).1 hm i hi)]; exact K.lounges T e x χ H i V
    rw [if_neg (fun hz=>hm ((mem_filter.mp hz).2))]; obtain ⟨i,hi,hv⟩:∃ i∈ Z,¬ agreesD d (tick τ i):=by by_contra! hg; exact hm ((connection (x:=x) d τ Z hp.1 h).2 hg)
    exact prod_eq_zero hi (if_neg hv)
  next hp=> symm; exact sum_eq_zero fun i _=> if_neg fun h=>hp ⟨h.1,h.2.1⟩
lemma push_vector (F:Forest S.ratio)(V: Config G c) : HasSum (fun Z : Finset (Molecule S)=> overhead (prism T x χ o.K V F) R Q.table • (if joints T R Q.halo (radiusB x) Z ∧ permitsA x V Z then ∏ j∈Z, prance d τ R j Q.halo T x χ o.K Q.table W o.a V K.jingles else 0)) (S.push R.beta (K.printD d) V):=by
  let fz:=univ.filter (agreesD d)
  have hz: S.push R.beta (K.printD d) V=∑ A∈fz,S.push R.beta (K.openB A) V:= by
    unfold StepData.push printD fz; simp_rw [Finset.smul_sum]; exact integral_finsetSum _ fun i _=> StepData.push_slice (S.isKernel (funds_branch H.laws.intake.ready) _) _ _ (K.nutritive T x i H D e) -- fill
  rw [hz]; simp_rw [K.recued T d e x χ H D h, Finset.smul_sum]; exact hasSum_sum (s:=fz) (fun i _=> K.summons T e x χ H D F V i)
end Carat
end YM.PhysicalNext.Repeat.Lotus
