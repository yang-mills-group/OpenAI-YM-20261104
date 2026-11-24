import YM.OPE.Compatible.Minuet.Rotor
import YM.OPE.Compatible.Dent.Valve
/-!
# Actual block noise. Local reset. Translation. Exhaustive small-test.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open AnalyticBridge.VerifiedReset
open Next.Rank.Thirst
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : BudgetPoint} {m d M: ℕ} {W a r t σ E Λ μ x κ C w ε D: ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable {J:Seats F}{X Y:Support f}
def ordFrame (S:StepData c f) (q:Support c) (U:Config G f):=∀ j∈ q, S.patch.usesMin S.kernel (expandAt (S.ratio.embed j) U)
def ordBest (S:StepData c f) (q:Support c)(U:Config G f):=∀ k : S.Choices, ∀ j:Bond c,j.1 ∈ q → S.patch.usesBest S.kernel (S.connector U k.1 j)
def naked (S:StepData c f) (q:Support c) (m:ℕ)(U:Config G f) (r:ℝ):=∀ (i:Bond f), S.ratio.parent i.1∈ halo m q → G.chord (U i)≤ r
lemma helmet (Q:Patch)(K:KernelChoices)(h:Q.Branches K G):∃ r:ℝ, ∃ n:ℕ,0<r ∧ ∀ {c f:Side}(S:StepData c f),S.patch=Q→ S.kernel=K → ∀ U:Config G f,∀ q:Support c, naked S q n U r → ordFrame S (halo 1 q) U ∧ ordBest S q U:=by
    obtain ⟨r,d,hp,ht⟩:= FurtherK.approves Q K h
    refine ⟨r,d+1,hp,?_⟩; intro c f S hS hK U q hv
    have hs y (hy:y∈halo 1 q) (k:S.Choices):S.patch.usesMin S.kernel (expandAt (S.ratio.embed y) U) ∧
       ∀ a:Axis,S.patch.usesBest S.kernel (S.connector U k.1 (y,a)):=by
      rw [hK]; refine ht _ _ S hS hK U k y fun i hi=> hv i ?_
      obtain ⟨x,hx,hh⟩:=halo_spec.mp hy; refine halo_spec.mpr ⟨x,hx,(separation_triangle x y _).trans ?_⟩; change separation y (S.ratio.parent i.1)≤ d at hi; omega
    exact ⟨fun i hi=> (hs i hi (Classical.arbitrary S.Choices)).1,fun k ⟨i,a⟩ hi=> (hs i (halo_subset _ q hi) k).2 a⟩
section
variable {U:Config G f}{q:Support c}
lemma pairTag (p : Bond c)(hp:p.1∈ q) (h:ordFrame S (halo 1 q) U)(H:ordBest S q U) (k l:S.Choices) : S.prediction U k p=S.prediction U l p:=by
   rw [StepData.prediction,StepData.prediction,Patch.predict,Patch.predict,if_pos (H k p hp),if_pos (H l p hp)]; apply congr_arg; ext1 x; unfold StepData.connector StepData.frames Patch.frame; have ht: p.1+step p.2∈halo 1 q:= halo_spec.mpr ⟨p.1,hp,sep_step ..⟩; rw [if_pos (h _ (halo_subset _ _ hp)),if_pos (h _ (halo_subset _ _ hp)),if_pos (h _ ht),if_pos (h _ ht)]
variable (H:S.patch.Branches S.kernel G) (V:Config G c)
    (ht:∀ i,S.ratio.parent i.1∈halo (predReach S.patch+1) (qᶜ)→ (razed J U) i=U i)
include H ht
omit H in
lemma farGlow (j:Site c)(hj:j∉q):AgreeNear S.ratio.parent j (predReach S.patch+1) U (razed J U) := fun i hi=> (ht i (halo_spec.mpr ⟨j,mem_compl.mpr hj,hi⟩)).symm
variable (ha:ordFrame S (halo 1 q) U) (hb:ordFrame S (halo 1 q) (razed J U)) (hp:ordBest S q U)(hd:ordBest S q (razed J U))
include ha hb hp hd
lemma noscope (k:S.Choices) : S.likelihood U k=S.likelihood (razed J U) k:=by
   unfold StepData.likelihood; refine congr_arg₂ (·*·) (Finset.prod_congr rfl (fun j _=>?_)) (Finset.prod_congr rfl (fun j _=>?_))
   · by_cases h:j∈ q
     · unfold Patch.frameMass; rw [if_pos (ha _ (halo_subset _ _ h)),if_pos (hb _ (halo_subset _ _ h))]
     have hh:= (Emblems.frames_agree U (razed J U) _ k k H rfl ((farGlow ht j h).shrink (q':=j) (by rw [separation_self]; omega))).2
     exact mul_left_cancel₀ (by have := Fintype.card_pos (α:=S.patch.FrameTag); positivity) (show (Fintype.card S.patch.FrameTag:ℝ)*_= _ from hh)
   by_cases h:j.1∈q
   · unfold Patch.predictorMass; rw [if_pos (hp _ j h),if_pos (hd _ j h)]
   rw [(Emblems.choices U (razed J U) _ k k H rfl rfl rfl (farGlow ht j.1 h)).1]
lemma contour (β : ℝ) (k:S.Choices): S.density β U V=S.density β (razed J U) V * Real.exp (-tweak J (fun U=> β* noiseTaylor S V U k) U):=by
    let W:= razed J U;let z:= -tweak J (fun U=> β*noiseTaylor S V U k) U
    unfold StepData.density; rw [Finset.sum_mul]; refine sum_congr rfl fun i _=>?_ ; rw [noscope H ht ha hb hp hd i,mul_assoc]; apply congr_arg
    let e(e:Bond c) U (i:S.Choices):= G.price (V e*(S.prediction U i e)⁻¹)
    have he (b:Bond c):e b U i-e b W i=e b U k-e b W k:=by
       by_cases hv:b.1∈q
       · unfold e; rw [pairTag b hv ha hp i k,pairTag b hv hb hd i k]
       unfold e; rw [(Emblems.choices U W b i i H rfl rfl rfl (farGlow ht b.1 hv)).2.2,(Emblems.choices U W b k k H rfl rfl rfl (farGlow ht b.1 hv)).2.2]; rw [sub_self, sub_self]
    unfold StepData.noise StepData.penaltyWeight; rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,mul_assoc]; apply congr_arg; rw [← Real.exp_sum, ← Real.exp_sum,← Real.exp_add]
    apply congr_arg Real.exp; change (∑ b,-β*S.kernel.penalty*e b U i)= (∑ b,-β*S.kernel.penalty*e b W i) + z -- check plus
    simp_rw [← Finset.mul_sum]; have hE:(∑ b,e b U i)-(∑ b,e b W i)=(∑ b,e b U k)-(∑ b,e b W k):=by simp only [← Finset.sum_sub_distrib,he];
    change _= _ + -(β*(S.kernel.penalty*(∑ b,e b U k))-β*(S.kernel.penalty*(∑ b,e b W k))); nlinarith only [hE, congr_arg (fun m:ℝ=>β*S.kernel.penalty*m) hE]
end
end YM.PhysicalNext.Repeat.Aroma
