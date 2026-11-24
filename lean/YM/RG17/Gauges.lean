import YM.RG17.Gathers

/-!
# Finite-regulator simultaneous dollars (open producer `Depot.prices`)

to ambient `Returns` using the actual Order filter and SAME shift and
marked weights. It's okay if subsidiary limits depend on all fixed
measurements; always preserve the dollar budgets on that output, though!
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter MeasureTheory Extraction Table OPE OPE.Orbits RG12 SharpGram.Allow
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {C:Family G}{S:Table C.book}{f:Extraction.Order}{F:Spec.Final C f S}
    (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (H:Services C f S)
    {L:Layout F} (loc:Located L)(Z:Ledger L)
    {n:ℕ}{d:Fin n→ℕ}(p:Seats C d) {u R:ℕ}

def ledgerCoupling (L:Layout F) (r:ℝ)(i:UVIndex) :ℝ:= Pert.Asymptotics.regulatorRun C i.1 i.2 (L.level r)

variable {T:Type*}[NormedAddCommGroup T][NormedSpace ℂ T]
-- reports at finite regulator can use A directly, or if using intermediate
-- regulator coefficients, establish this comparison too.
def standing (L:Layout F)(v:ℕ→ℝ→ T)(R:ℕ) (r:ℝ) (i:UVIndex) : T:=
    ∑ j ∈ Finset.range (R+1), ((ledgerCoupling L r i : ℂ)^j) • v j r
lemma standingLimit (v:ℕ→ℝ→T)(R:ℕ)(r:ℝ): Tendsto (standing L v R r) L.lens (𝓝 (accrue Z R v r)):=by
    apply tendsto_finsetSum _; intro j _
    have h:= (Z.fuse_at r).mono_left L.certified
    change Tendsto (fun (i:UVIndex)=> ((ledgerCoupling L r i:ℂ)^j) • v j r) L.lens _
    rw [wt,Complex.ofReal_pow]
    exact (((Complex.continuous_ofReal.continuousAt (x:=Z.g r)).tendsto.comp h).pow _).smul tendsto_const_nhds

variable (A:Ports C) (v:(i:Fin n)→ Slot C (d i))(D:ℕ)(K:Set (Points n))(W:Finset (External C S))
structure ActualReport (loc:Layout F) (Z:Ledger loc) (A:Ports C) (v:(i:Fin n)→Slot C (d i)) (D:ℕ) (p:Seats C d)(W:Finset (External C S)) (K:Set (Points n))(R:ℕ) : Prop where
    estimates : ∃ (a c η:ℝ) (k t:ℕ), 0<a ∧ 0≤c ∧ 0 ≤ η ∧ η ≤ 1 ∧ ∀ᶠ r in home,
      ∀ ψ:Test n,tsupport ψ ⊆ K → ∃ M:UVIndex → C.label D,
        ∀ b:ℝ,Demand t ψ b → ∀ᶠ i in loc.lens, -- constants fixed; regulators taken after test/radius
          (∀ X∈ W, ‖bank loc p r ψ X i - headMark loc X D r i (M i)‖ ≤ c*r^((D:ℝ)+a)*b) ∧
          ‖M i-standing loc (fun j r=> A.marked v D j r ψ) R r i‖≤ c* ledgerCoupling loc r i ^ ((R:ℝ)+1 - η) * Z.Λ r^k * b

include H P loc
set_option maxHeartbeats 400000 in
lemma ranked (h:ActualReport L Z A v D p W K R) (hv:Weights L v p)(hk:IsCompact K)(hx:K⊆conf n) :
  ∃ M:Test n→ℝ→ C.label D, TestedOutput L v D W K M ∧ Cost Z (jointTests K) R (fun r ψ=> M ψ r - forecast Z R (A.marked v D) r ψ):=by
    obtain ⟨a,c,η,k,t,ha,hc,hη,hη',H₁⟩:= h.estimates
    let f(r:ℝ)(ψ:Test n)(m:C.label D): Prop:= tsupport ψ⊆K → ∀ b:ℝ,Demand t ψ b→
       (∀ X∈ W, ‖appeared F (stems L v r) X r ψ - X.charge F D (master L D r m)‖ ≤ c*r^((D:ℝ)+a)*b) ∧
       ‖m - forecast Z R (A.marked v D) r ψ‖≤ c* Z.g r ^ R * Z.Λ r^k * b
    let αs (r:ℝ):= c*r^((D:ℝ)+a)
    have hc₁:∀ᶠ r in home,∀ ψ:Test n,∃ m:C.label D,f r ψ m:=by
       filter_upwards [H₁,Z.small,(eventually_all_finset W).mpr (fun X _=>limitBank P H L loc X p hv hk hx),loc.level.growing.eventually_ge_atTop (C.ref D)] with r hr hsmall hu hk ψ
       by_cases h:tsupport ψ⊆K; swap
       · exact ⟨0,fun k=> False.elim (h k)⟩
       obtain ⟨M,hM⟩:= hr ψ h
       obtain ⟨b,hb⟩:= demandAccessible t ψ
       letI := L.notbot
       let L' := L.lens; let u:= (R:ℝ)+1-η; let σ (i:UVIndex):=ledgerCoupling L r i
       let t' i:= c * σ i ^ u * Z.Λ r^k; let y:=c * Z.g r ^ u * Z.Λ r^k
       have hσ:Tendsto σ L' (𝓝 (Z.g r)):= (Z.fuse_at r).mono_left L.certified
       have hY:Tendsto t' L' (𝓝 y):=((hσ.rpow_const (.inl (Z.positive r).ne')).const_mul _).mul_const _
       let z(j:ℕ)(r:ℝ):= A.marked v D j r ψ; let q:= standing L z R r; let Q:= forecast Z R (A.marked v D) r ψ
       have hq:Tendsto q L' (𝓝 Q):= standingLimit Z z R r
       have hp:∀ᶠ i in L',‖M i‖≤ ‖Q‖+ y*b + 1:=by
          filter_upwards [(hM b hb), ((hq.norm).add (hY.mul_const b)).eventually (gt_mem_nhds (lt_add_one (‖Q‖+y*b)))] with i hm hy
          refine le_trans (norm_le_norm_add_norm_sub (q i) (M i)) ?_
          rw [norm_sub_rev]; exact (add_le_add_right hm.2 ‖q i‖).trans hy.le
       obtain ⟨g,hg,Hg,m,hm⟩:= Next.UVStress.finite_extract M _ hp
       have hy : Z.g r ^ u ≤ Z.g r ^ R:=by rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_ge (Z.positive r) hsmall (by unfold u; linarith)
       refine ⟨m,fun _ b hb=>?_⟩; constructor
       · intro X hx; apply le_of_tendsto (((hu X hx ψ h).mono_left hg|>.sub (limitHead L X hg hm hk)).norm)
         filter_upwards [(hM b hb).filter_mono hg] with i h; exact h.1 X hx
       refine le_trans (le_of_tendsto_of_tendsto ((hm.sub (hq.mono_left hg)).norm) (((hY.mono_left hg).mul_const b)) (((hM b hb).mono fun i hi=>hi.2).filter_mono hg)) ?_
       exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy hc) (pow_nonneg (zero_le_one.trans (Z.above r)) _)) hb.nonneg
    let M(ψ:Test n)(r:ℝ):= if h: ∃ m:C.label D,f r ψ m then h.choose else 0
    have hM:∀ᶠ r in home,∀ ψ:Test n,f r ψ (M ψ r):= hc₁.mono fun r hr ψ=>by dsimp only [M]; rw [dif_pos]; exact (hr ψ).choose_spec
    exact ⟨M,⟨a,c,t,ha,hc,hM.mono fun r hr X hx ψ hψ b hb=>(hr ψ hψ b hb).1 X hx⟩,c,k,t,hc,hM.mono fun r hr ψ b hp=>(hr ψ hp.1 b hp.2).2⟩

structure Depot (Z:Ledger L)(A:Ports C)(v:(i:Fin n)→ Slot C (d i))(D:ℕ)(K:Set (Points n))(u:ℕ) : Prop where
    prices : ∀ W:Finset (External C S), ∃ (p:Seats C d)(R:ℕ), u<R ∧
      Weights L v p ∧ (∀ j≤R,Cost Z (jointTests K) 0 (A.marked v D j))∧ ActualReport L Z A v D p W K R
lemma toReturns (h:Depot Z A v D K u) (hk:IsCompact K)(hx:K⊆conf n):Returns Z A v D K u:=by
    constructor; intro W; obtain ⟨p,R,hu,hp,he,H'⟩:= h.prices W; exact ⟨R,hu,he,ranked P H loc Z p A v D K W H' hp hk hx⟩

end YM.RG17
