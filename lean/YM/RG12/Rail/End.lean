import YM.RG12.Rail.Price
/-! Two-sided relative price at all illuminated unit STEPS, and remains a
leading relative comparison to free (not an absolutely sharp step price in beta units).
Exports ready for pricing across the chain -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Rail
open Function Filter Set Finset Lattice Wilson RG Next.Rank Next.Rank.Atlas Station Prayer Perch Glimmer Real
open Extraction Bid MergeProof Source Org Spec PhysicalNext PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank.Soft
open MergeProof.East Arche Shapes Roof RG12.Frames RG12.Desk.Paired
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{ϕ : Filter UVIndex}[ϕ.NeBot] {M : ∀ d, ℕ→RepChart C d} {d n:ℕ}
 {ι:Type}[Fintype ι] {W:Bid.Worth}{u ψ β δ:ℕ→ℝ}{r:ℕ→ℕ}
open PhysicalNext.Repeat.Legato.Bandage Next.Rank.Tapes.West
variable {L:∀ N p m:ℕ,m<N→MergeProof.GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (T:ι → Tapes.Panel d) (B:Binding C)(H:C.Makes)(h:G.Simple)(hp:Scrim C W u ψ β δ (fly C.path.levels) r L) (O:HaarBudget G)(J:Precision.ChartRatio G)
set_option quotPrecheck false
local notation "A" => C.path.levels
variable (z:ℝ) (hZ : ∀ i≤d,MergeProof.Accent.generator G i ≤ z) (index:ι)
local notation "a!"=> (T index).arc
local notation "cK" k:max => (A).clock.hatBeta k
local notation "cheap" x:max k:max=> bill x (cK k)
local notation "Y$" k:max=> mag (A) a! k
variable {S : Table C.book} {f: Extraction.Order}(F:Final C f S)(hQ:Observing C H ϕ M)(hb:ϕ ≤ f.fuse)(hn:2≤n)
local notation "V!"=>Desk.Sector F.sector.derivatives d
local notation "X!"=> Frames.Col (V!)
omit [Fintype ι] [ϕ.NeBot] in
private lemma print₀ :0 ≤ cut₀ n:=by unfold cut₀ σ₀; positivity -- no includes by default. change
include hn h
private lemma goes : Tendsto (fineprint (A) n) atTop (𝓝 0) := by
   have he:0<(n:ℝ):=by exact_mod_cast (lt_of_lt_of_le (by decide) hn:(0:ℕ)<n)
   have hx : 0 < cut₀ n:= by unfold cut₀ σ₀; positivity
   exact (bill_hi (neg_lt_zero.mpr hx)).comp (hat_rate _ h)
set_option linter.unusedSectionVars false
include hQ hb hn H h hp hZ
lemma beacon_cost (hs:Slugg (A))(ax:Axis)(q:OPE.Prescription F.sector.derivatives)(hq:q.Coherent) :
    ∃ (K:ℝ),1 ≤ K∧∀ᶠ N:ℕ in atTop,∀ᶠ k:ℕ in atTop,
      ∀ (Z:∀ i:Fin (d+1),Module.End ℂ (C.label i)), Good (n:=n) (ϕ:=ϕ) T B H O J z index Z k→
      let x:=stepLense F d M k Z N a!; let l(k):=torchR (A) a! N k
      let R k:= sampleForm F (Shapes.scope ax N) d (l k)
      (Frames.triangular (V!) ((Desk.official q hq d).symm.toLinearMap.comp x) ∧ RG12.Frames.Gram.Regular (R k) x K):=by
   obtain ⟨K,hK,hv⟩:=Roof.base F d ax
   have hkc : 0 < K:=zero_lt_one.trans_le hK
   refine ⟨2*K,by linarith only [hK],?_⟩
   filter_upwards [hv,eventually_gt_atTop 0] with N hk hn₀
   have hc:0 < a!:=by have e:=(T index).huge; linarith [Nat.cast_nonneg (α:=ℝ) d]
   filter_upwards [tour_clock (A) h a! hc hs N hn₀ n d hn,available T B H h hp O J z hZ index F hQ hb hn hs ax N hn₀,(goes (C:=C) h hn).eventually (ge_mem_nhds (show 0<(2*K)⁻¹ from by positivity))] with k h1 h2 h3 Z hZ x l R
   refine ⟨?_,Gram.nonsingular (fun v=>(Roof.white F d ax N v v).re) hK hk (fun v=> le_trans ?_ (mul_le_mul_of_nonneg_right h3 (sq_nonneg _)))⟩
   · intro i j hj v; exact (triangular.comp (Roof.aim F d q hq M k Z) (tri_dilate (drift (A) a! N k))) i j hj v
   apply (h2 Z hZ _ h1.1 h1.2.2.1 v)

lemma slopes (hs:Slugg (A))(ax:Axis)(q:OPE.Prescription F.sector.derivatives)(hq:q.Coherent):∃ K:ℝ,1 ≤ K∧ ∀ᶠ N:ℕ in atTop,∀ᶠ k:ℕ in atTop,
   let T₁:=stepLense F d M; let τ(k):=torchR (A) a! N k
   let u:=τ k/τ (k+1); let H k: S.Field d →ℝ:= Real.sqrt ∘ (sampleForm F (Shapes.scope ax N) d (τ k)).eval
   let e:=fineprint (A) n k
   ∀ (Z:ℕ→ ∀ i:Fin (d+1),Module.End ℂ (C.label i)),Good (n:=n) (ϕ:=ϕ) T B (F.room.cutoff) O J z index (Z k) k→Good (n:=n) (ϕ:=ϕ) T B (F.room.cutoff) O J z index (Z (k+1)) (k+1)→
   ∃ X Y: Col (V!)≃ₗ[ℂ] S.Field d, X.toLinearMap=T₁ k (Z k) N a!∧Y.toLinearMap=T₁ (k+1) (Z (k+1)) N a!∧
     1 ≤ u∧∀ v, H k (Y (Frames.dilate u v)) ≤ (1+4*K*e)*H (k+1) (Y v) ∧ H (k+1) (Y v) ≤ (1+4*K*e)*H k (Y (Frames.dilate u v)):=by
   obtain ⟨K,hK,h₀⟩:= beacon_cost T B H h hp O J z hZ index F hQ hb hn hs ax q hq
   have he:=zero_lt_one.trans_le hK
   refine ⟨K,hK,?_⟩
   let ω:=fineprint (A) n
   filter_upwards [h₀,eventually_gt_atTop 0] with N hH hN
   have hT:Tendsto (fun i=>4*K*ω i) atTop (𝓝 0):=by simpa using (goes (C:=C) h hn).const_mul (4*K)
   filter_upwards [hH,(tendsto_add_atTop_nat 1).eventually hH,(bloc T B H h hp O J z hZ index F hQ hb hn hs ax N hN), hT.eventually (ge_mem_nhds zero_lt_one)] with k h1 h2 h3 h4 T₁ τ t H' e Z hK₀ hK₁
   obtain ⟨hσ,hX⟩:=h1 (Z k) hK₀
   obtain ⟨hτ,hY⟩:=h2 (Z (k+1)) hK₁
   let Ω l:=stepLense F d M l (Z l) N a!
   let V:=Desk.Sector F.sector.derivatives d; let D:=Frames.Col V
   have hi {k:ℕ}(hY:Gram.Regular (sampleForm F (Shapes.scope ax N) d (τ k)) (Ω k) K) : Bijective (Ω k):=by
      let P:=Desk.official q hq d
      have hB:Injective (Ω k):= LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (by
        intro x hx
        apply norm_le_zero_iff.mp; have hG:= hY.coerc x; rw [hx,Gram.Square.zero,mul_zero] at hG
        exact le_of_pow_le_pow_left₀ (n:=2) (by norm_num) le_rfl (hG.trans_eq (zero_pow (by norm_num:2≠0)).symm)))
      exact ⟨hB,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank P.finrank_eq).mp hB⟩
   let l(l : ℕ)(hp :Bijective (Ω l)) := LinearEquiv.ofBijective _ hp
   have h₀:= h3 _ _ hK₀ hK₁
   obtain ⟨hx,-⟩:= h₀ (0:D)
   refine ⟨l _ (hi hX), l _ (hi hY), rfl,rfl,hx,fun v=>?_⟩
   let x:=Ω (k+1) v; let y:=Ω (k+1) (Frames.dilate t v)
   let G0 := (sampleForm F (Shapes.scope ax N) d (τ k)).eval y; let G1:= (sampleForm F (Shapes.scope ax N) d (τ (k+1))).eval x
   change Real.sqrt G0 ≤ (1+4*K*e)*Real.sqrt G1 ∧ Real.sqrt G1 ≤ (1+4*K*e)*Real.sqrt G0
   obtain ⟨-,-,hv,hq'⟩:= h₀ v
   have hb' := hY.coerc v; change ‖v‖^2 ≤ K*G1 at hb'
   have hz₁:0≤G1:=nonneg_of_mul_nonneg_right ((sq_nonneg _).trans hb') he
   have hE: 0 ≤ e:= show 0 ≤ bill _ _ from (Real.exp_pos ..).le
   obtain ⟨ha,hv⟩:= abs_le.mp hv; obtain ⟨hl,hρ⟩:= abs_le.mp hq'
   let P:= (Roof.white F d ax N v v).re
   change -(e*‖v‖^2) ≤ G0-P at hl; change G0-P ≤ _ at hρ
   change -(e*‖v‖^2) ≤ G1-P at ha
   change G1-P ≤ e*‖v‖^2 at hv; change G0-P ≤ e*‖v‖^2 at hρ
   let η:=2*K*e; have hm : 2*η ≤ 1:=by change 4*K*e ≤ 1 at h4; unfold η; linarith
   have hη:0 ≤ η:=by unfold η; positivity
   have hD : (1-η)*G1 ≤ G0 ∧ G0 ≤ (1+η)*G1 := by
      unfold η; constructor <;> nlinarith only [ha,hv,hl,hρ,mul_le_mul_of_nonneg_left hb' hE]
   have hz₀ :0 ≤ G0:= (mul_nonneg (by linarith) hz₁).trans hD.1
   have hA {x y:ℝ}(hx:0 ≤ x)(hy:0 ≤ y)(hw:x ≤ (1+2*η)*y): Real.sqrt x ≤ (1+4*K*e)*Real.sqrt y:=by
      have hB:1+4*K*e=1+2*η:=by unfold η; ring
      rw [hB]
      apply le_of_pow_le_pow_left₀ (n:=2) (by decide) (by positivity)
      rw [Real.sq_sqrt hx,mul_pow,Real.sq_sqrt hy]; exact hw.trans (mul_le_mul_of_nonneg_right (le_self_pow₀ (by linarith) (by decide)) hy)
   refine ⟨hA hz₀ hz₁ (hD.2.trans (mul_le_mul_of_nonneg_right (by linarith) hz₁)),hA hz₁ hz₀ ?_⟩
   have hf:1 ≤ (1-η)*(1+2*η):=by nlinarith
   nlinarith only [mul_le_mul_of_nonneg_right hf hz₁, mul_le_mul_of_nonneg_left hD.1 (show 0≤1+2*η by linarith only [hη])]
end YM.RG12.Rail
