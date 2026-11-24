import YM.RG12.Canonical.Ticket
import YM.RG12.Budget.Logs
import YM.OPE.Log.Bottleneck
import YM.OPE.Exchange.Arrangement

/-!
# Check the available weaker bounds on these exact limit matrices

Include the actual inverse off shell as a temporary fixed-k weak estimate, not as a demand
for a lower bound on a redundant physical list. And check in Lean that the `fare` outlet can't
pay a matrix precision budget in powers of coupling even with *any* additional internal order
paid multiplicatively. Doesn't rule out detector cancellation or compensating spatial errors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12
open Function Filter Finset Lattice RG Source OPE Columns Table
open Next.Extract Dash MeasureTheory Analysis Spec
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {C:Family G} (hc:C.Makes) {f:Extraction.Order}
variable {S : Table C.book} {V : DiffPlan S} (H:Services C f S)(he:V.Inclusions S)
    {M:∀ d:ℕ,ℕ→ RepChart C d}{b:Filter UVIndex}[b.NeBot] (hq:b≤ f.fuse)(h:Observing C hc b M)
include hc

/-- A simple inverse off shell at every fixed k (prefix-product costs). -/
lemma go_finer (d k : ℕ) (i:UVIndex) (h1:C.ref d ≤ k)(h2:k ≤ i.1)(x:C.label d):
    mass C d (charts C hc d k i x) ≤ juice C.path.levels k * mass C d x:=by
    let T:= C.factory d i.1 i.2; let B:= T.terminal; let X i:= (T.entries i (T.terminal.symm x)).x
    have hp:=hc.calibrated d i.1 i.2 (h1.trans h2)
    rw [← quota_charts _ hc _ _ i h1 h2]
    change mass _ d (X k) ≤ _
    induction k,h1 using Nat.le_induction with
    | base=>
      rw [show X (C.ref d)=x from C.normalized hc h2 _]
      exact le_mul_of_one_le_left (mass_nonneg ..) (juice_pos ..)
    | succ k he ih=>
      let Q:= C.path.levels; let s:= (Q.params (k+1)).columns
      change mass _ _ (X _)≤ _
      rw [juice_step,mul_assoc]
      refine (hp.back k he h2 _).trans ?_
      exact mul_le_mul_of_nonneg_left (ih ((Nat.le_succ k).trans h2)) (zero_le_one.trans (Q.params _).columns_ge)
include h
lemma observes_coerc (d k:ℕ)(hk:C.ref d ≤ k)(x:C.label d) :
    mass C d x ≤ juice C.path.levels k * mass C d (M d k x):=by
  let y i:= atK C hc d k i x; have hu:=h.columns d k hk x le_rfl
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (((continuous_mass C d).continuousAt.tendsto.comp hu).const_mul _)
  filter_upwards [h.grows.eventually_ge_atTop k] with i hi
  have he:= go_finer hc d k i hk hi (y i)
  rw [show charts C hc d k i (y i)= x from LinearEquiv.apply_symm_apply ..] at he; exact he

lemma weak_inside (S:Table C.book)(d k : ℕ)(hk:C.ref d ≤ k):
    ∀ x:S.Field d,∃ v:C.label d,S.project d (M d k v)=x ∧ mass C d v≤ juice C.path.levels k * mass C d (S.representative d x):=by
    intro x
    have hi : Injective (M d k).toLinearMap:= LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (by
       intro v hv
       have hv': M d k v=0:=hv
       have he:‖v‖ ≤ 0 := (norm_le_mass ..).trans ((observes_coerc hc h d k hk v).trans (by simp [mass,hv',Labels.Frame.coeffSize]))
       exact norm_le_zero_iff.mp he))
    obtain ⟨v,hV : M d k v = S.representative d x⟩:= (LinearMap.injective_iff_surjective.mp hi) (S.representative d x)
    exact ⟨v,hV ▸ S.rep .., hV ▸ observes_coerc hc h _ _ hk v⟩

include H he hq
lemma weak_outside (d w k : ℕ)(hk:C.ref d ≤ k)(h0:w<d) (L:S.Field d→ₗ[ℂ]ℂ) (hl:∀ x:S.Field w,L (V.rise h0.le x)=0)(x:C.label d) :
    ‖L (S.project d (M d k x))‖ ≤ ‖LinearMap.toContinuousLinearMap (L.comp (S.project d))‖ * fare C k d w * mass C d x:=by
    obtain ⟨_,hG,H0,H⟩:=H; obtain ⟨W,r,D,T⟩:=H0; obtain ⟨A,U,R,Z,B⟩:= H
    obtain ⟨v,hv,ht⟩:=h.purchase d k hk le_rfl x
    obtain ⟨y,⟨p,hp⟩,hP⟩:=limit_cap T.toTableTickets hG B he h0 v _ hq hk ht hv
    let Q:= LinearMap.toContinuousLinearMap (L.comp (S.project d))
    rw [show L (S.project d (M d k x))=Q (M d k x-y) from ?_]
    · refine (Q.le_opNorm _).trans ((mul_le_mul_of_nonneg_left hP (norm_nonneg _)).trans_eq ?_); rw [mul_assoc]
    change _=L (S.project d _); rw [map_sub,map_sub,← hp,hl,sub_zero]

/- `not_fee` even with an arbitrary finite coupling order bought against a target price here.
actual regulator beta can use ANY cutoff and period eventually admitted. -/
omit H h hq he
include hc
lemma still_not_fee {ψ:Filter ℕ}[ψ.NeBot] (hT:ψ ≤ atTop)(hG:G.Simple)
    (m p:ℕ→ℕ)(hp:∀ᶠ i in ψ,i≤ m i) (d w R :ℕ):
    ¬ Wallet ψ C.path.levels.clock.hatBeta (fun i=> C.S.a i^(d-(w+1)) * fare C i d w * Pert.Asymptotics.regulatorRun C (m i) (p i) i ^ R):=by
    let g i:=Pert.Asymptotics.regulatorRun C (m i) (p i) i; let v i:=C.path.β (m i) (p i) i; let s:=G.slopeConstant; let B:=C.path.levels.clock; let b:=B.hatBeta
    have ht:=Budget.energy_grows hc hG (p:=p) (m:=id) (N:=m) (l:=ψ) hT hp -- id map
    have hs:= Gauge.slopeConstant_pos hG; change 0<s at hs
    have he:∀ᶠ i in ψ,v i ≤ 4*b i:=by
       filter_upwards [(Pert.Asymptotics.zeroUp_bound C hc hs).filter_mono hT,(C.S.divergent.eventually_gt_atTop 0).filter_mono hT,hp,(hat_grows (C:=C) hG|>.eventually_ge_atTop (-B.bar)).filter_mono hT] with i hr hh hm hB
       have hx:=hr (m i) (p i) hm; rw [Pert.Asymptotics.b0_normalizes] at hx; obtain ⟨-,hk⟩:=abs_lt.mp hx
       have he:v i< (2*s)*C.S.scale i:=(div_lt_iff₀ hh).mp (by linarith [hk]); change -B.bar ≤ B.bar+s*C.S.scale i at hB; change v i ≤ 4*(B.bar+s*C.S.scale i); linarith only [he,hB]
    have hZ:= (hat_grows (C:=C) hG).mono_left hT; have ht:∀ᶠ i in ψ,1≤v i:= ht.eventually_ge_atTop 1
    have hx: Wallet ψ b (g⁻¹) :=by
      refine ((Wallet.const hZ (4:ℝ)).mul (Wallet.id hZ)).transfer ?_
      filter_upwards [he,ht] with i ha hu
      change ‖(g i)⁻¹‖ ≤ _; have hS:=Real.sqrt_nonneg (v i); have hV := Real.sq_sqrt (zero_le_one.trans hu)
      rw [show g i=(Real.sqrt (v i))⁻¹ from rfl,inv_inv,Real.norm_of_nonneg hS]
      exact (show Real.sqrt (v i) ≤ v i by nlinarith only [hS,hV,hu]).trans (ha.trans (Real.le_norm_self _))
    intro H; have hJ:= H.mul (hx.pow hZ R)
    apply OPE.Log.not_fee hT hG d w; apply hJ.congr; filter_upwards [ht] with i hi
    change _ *g i^R*(g i)⁻¹^R=_; have hg: g i ≠ 0:=((inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le hi))):0< (Real.sqrt (v i))⁻¹).ne'
    rw [mul_assoc,inv_pow,mul_inv_cancel₀ (pow_ne_zero _ hg),mul_one]
end YM.RG12
