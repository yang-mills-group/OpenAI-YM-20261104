import YM.LocalLTE.Port.Moon
/-! # non-Model regular parts; uses values only but keeps physical support and source origin in ℕ book. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Set Lattice RG Pressure Wilson Finset MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus FrameBox Cabana Push
open Progress.DirectedRecipe MergeProof Menu Marker Accent Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge}{c f : Side}{Q : Rep G f} {S:StepData c f} {σ κ Λ μ' w t v : ℝ}
variable {V I J : Type}[DecidableEq V][Fintype V] {R:Marker.Census V}(B:Bands R Q)(r:V→ℝ) (hr:∀ i,0<r i) (o:V→Site f)
open Extra.Trajectories Next.Foundations
variable {d U:ℕ} {a₀ c₁ a β:ℝ}
local notation "P"=> Q.p
local notation "ν"=> Q.p.threshold
local notation "W₀"=> Config G f
variable (h:B.Active)(hw:B.Radial r a₀ a v c₁)
open Push.AbsoluteSums Push.AbsoluteSums.Animals
local notation "TT"=> FamilyE B
-- lease. Counts.NB avoid parity sum fee via bool.L.Color.Scope.Future.
-- ghost entry none.Membership ray actual nonzero? supports B.active unconditionally all rays.
abbrev Berry (B:Bands R Q):= {p: R.Mode × Support f // p.1.val.Nonempty∧ p.1.val.image B.origins⊆ p.2}
def desk (p:Berry B): RegularAddress f:= ⟨B.origins (Classical.choose p.property.1),p.val.2,p.property.2 (Finset.mem_image_of_mem _ (Classical.choose_spec p.property.1))⟩
include h hw
variable (hm:HasSlots Q.p Q.activities)(e:(Berry B)×Bool ↪ ℕ)
include hm
lemma stow : ∃ F:(Berry B) × Bool→ Menu.Hat R Q,(∀ i,(F i).M.turn=.logKey (blankRow f (desk B i.1,e i)))∧ PL B.origins F ∧ (∑ i, sumFee (F i) r*Q.p.mass (F i).M.crest (F i).M.weight) ≤ 2*(((Fintype.card V):ℝ)*a)∧ ∀ x,roll F x=∑' j,B.ray j x:=by
    let Y(i:ℕ): Berry B:=⟨(B.rays i,B.support i),h.proper _, fun p hp=>by obtain ⟨v,hx,rfl⟩:= Finset.mem_image.mp hp; exact h.pins _ _ hx⟩
    let Z:=fun i=> masked ν (B.support i) (B.H i); let X:=desk B; let x(p):= (X p).support; let k(p:Berry B):= p.val.1
    let u (p:Berry B) z:= cram Y (fun i=> Z i z) p
    obtain ⟨b,hb,hH⟩:= hw.bulk; let t:= cram Y b; let f₀ (i):= Poly.toll r (B.rays i) * (P).mass (B.support i) (b i)
    have hg(i): 0 ≤ f₀ i:= mul_nonneg (Poly.worth hw.pure _|>.le) (mul_nonneg (Real.exp_nonneg _) (hb _|>.1))
    have hv: SumBudget f₀ _:= Overlay.per_system hg h.proper hH
    have hp (i):0≤ b i:= (hb i).1
    have hz: Summable b:= Port.everyone r hw.pure P x k Y b hv hp
    have hs i j: Sale Q.p (x (Y i)) (fun V=> scaleQ j (Z i V)) (b i):=by
        obtain ⟨o,ho⟩:= h.proper i; obtain ⟨hx,hJ⟩:= Port.framesV (h.regular i) ((hb i).2 o ho) j
        rw [show (fun V=>scaleQ j (Z i V))= _ from funext (fun V=> (Port.stratum (G:=G) (S:=B.support i) V j ν (B.H i)).symm)]
        exact Port.supportQ Q.p _ hx hJ -- namespace argument
    let g (p:Berry B) (j:Bool) (V):= scaleQ j (u p V)
    have hT(V) (i): ‖Z i V‖ ≤ b i:=by
       obtain ⟨o,ho⟩:= h.proper i; by_cases H:Healthy ν (B.support i) V; · unfold Z; rw [masked_eq _ _ _ _ H]; exact ((hb i).2 o ho).2 V H [] (by simp) (by simp)
       unfold Z; rw [masked_ne _ _ _ _ H,norm_zero]; exact hp i
    have hU V:Summable (fun i=>Z i V):= hz.of_norm_bounded (hT V)
    have he(p)(j):Sale P (x p) (g p j) (t p):=by
       let K:= {i// Y i=p}; let f (i:K) V:= scaleQ j (Z i.val V)
       have he : g p j = fun V=> ∑' i,f i V:=by ext V; unfold g f u cram; rw [ContinuousLinearMap.map_tsum]; exact (hU V).comp_injective Subtype.val_injective
       have hv (i:K): Sale P (x p) (f i) (b i.val) := by obtain ⟨i,hi⟩:=i; dsimp only [f]; have h:= hs i j; rw [hi] at h; exact h
       have hW := hz.comp_injective (show Injective (Subtype.val : K→_) from Subtype.val_injective)
       rw [he]; refine ⟨fun U V ht hU=> tsum_congr fun i=> (hv i).reads U V ht hU,fun z V=> tsum_congr fun i=> (hv i).gauge z V,Measurable.tsum (fun i=> (hv i).meas),fun U=> ?_,fun U h=>?_⟩
       · have H (i): ‖f i U‖ ≤ b i.val:= (hv i).norm U; have hh : Summable (fun i=>‖f i U‖):= hW.of_nonneg_of_le (fun i=> norm_nonneg _) H; exact (norm_tsum_le_tsum_norm hh).trans (hh.tsum_le_tsum H hW)
       by_contra H; exact h ((tsum_congr fun i=>Classical.byContradiction (fun hh=> H ((hv i).marks _ hh : Healthy ν (x p) U)) : ∑' i,f i U=∑' _:K,(0:ℝ)).trans tsum_zero)
    let hZ (p:Berry B): (k p|>.val).Nonempty ∧ (k p|>.val).image B.origins⊆ (X p).support:= p.property
    let F:= lea B.origins X k t hZ g he hm e
    have hL:= joinsL B.origins X k t hZ g he hm e
    refine ⟨F,fun i=>rfl,hL,?_,fun V=>?_⟩
    · unfold F; rw [prices r B.origins X k t hZ g he hm e t (fun _=>rfl)]; exact mul_le_mul_of_nonneg_left (Port.wholeQ r Q.p x k Y b hv) zero_le_two
    exact Port.mother _ X k t _ g he hm e Y Z hU (fun _ _ _=> rfl) _
end YM.LocalLTE.Port
