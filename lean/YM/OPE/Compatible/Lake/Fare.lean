import YM.OPE.Compatible.Lake.Frame
/-! Guard norms of output route observed through same shawdow. Use character estimates? don't need: limits on projections are at unselected fixed Final. Cost proved even with differing books on projections. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter MeasureTheory Spec Lattice RG Word Cov Allot MergeProof Next.Extract Dash Extra.Histories
open Next.Rank Next.Rank.Price Extraction
open ContinuousLinearMap
open scoped Topology Classical BigOperators
variable {d k N:ℕ}{G:Gauge}{C:Family G}{T:C.Makes}
set_option quotPrecheck false
local notation "F" => C.label d
local notation "L" => C.labels.level d
variable {Q:ℕ→ C.label d ≃L[ℂ] C.label d}{φ:Filter (ℕ×ℕ)} [φ.NeBot]{H:Extraction.Order}(M:Conic T φ Q)
variable (h:φ ≤ H.fuse) (hk:C.ref d ≤ k)
local notation "A₀" => OPE.Columns.juice C.path.levels k
variable {W : Table C.book} {P:DiffPlan W}{e:ℕ}(pi:P.Inclusions W) (v : W.Field d→L[ℂ]ℂ) (κ : Services C H W)
    (hV:∀ (j:ℕ),j < e → ∀ h:j ≤ d,∀ y:W.Field j,v (P.rise h y)=0) (he:e ≤ d)
include pi hV κ he M h
lemma spotted : ∃ c:ℕ→ℝ, (∀ i:ℕ,0 ≤ c i) ∧ RateLE atTop C.S.scale c ((d-e:ℕ):ℝ) ∧ ∀ k:ℕ,C.ref d≤k→∀ x:C.label d, ‖v (W.project d x)‖ ≤ c k * chargeTerm d x (Q k):=by
    let u:= v.comp (LinearMap.toContinuousLinearMap (W.project d)); obtain ⟨W0,x,hq,hX⟩:=κ.purchase -- W name duplicate!
    obtain ⟨A,S,Y,p,hB⟩:=κ.along
    cases e with
    | zero=>
       let c i := ‖u‖*(OPE.Columns.juice C.path.levels i*(C.S.a (C.ref d) / C.S.a i)^d)
       have ht: RateIs atTop C.S.scale C.S.a (-1):=by exact ⟨Eventually.of_forall C.S.a_pos, Ribbons.Note.note_a C.S|>.pitch⟩
       have hp:= ht.rate
       refine ⟨c,fun i=> mul_nonneg (norm_nonneg _) (mul_nonneg (zero_le_one.trans (OPE.Columns.juice_pos ..)) (pow_nonneg (div_nonneg (C.S.a_pos _).le (C.S.a_pos _).le) _)),?_,fun k hk x=>?_⟩
       · have heq:= ((RateLE.const ‖u‖ C.S.divergent).mul (((OPE.Columns.juice_rate C).mul (((RateIs.const C.S.divergent (C.S.a_pos (C.ref d))).div ht).power d)).pays C.S.divergent)); simpa using heq
       have hh:= tallyRange (p:=x) _ M h hk (u:=fun _=>x) tendsto_const_nhds -- named p conflict
       let a := OPE.Columns.juice C.path.levels k*((C.S.a (C.ref d) / C.S.a k)^d)
       have hu: ‖x‖ ≤ a* chargeTerm d x (Q k):= ge_of_tendsto (hh.const_mul _) (((Push.RelayDifference.cutoff_grows H).eventually_ge_atTop k).filter_mono h|>.mono fun i hi=> OPE.Columns.whole_origin hB x hk (p:=i.2) hi)
       exact ((u.le_opNorm x).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _))).trans_eq (by dsimp only [a,c]; ring)
    | succ i =>
       let r:= (OPE.Columns.fare C · d i)
       have hr: RateIs atTop C.S.scale r (d-(i+1):ℕ):=by
          have hz: Tendsto (fun j:ℕ=> C.S.scale j/C.S.scale j) atTop (𝓝 1):=tendsto_const_nhds.congr' ((C.S.divergent.eventually_gt_atTop 0).mono fun j hj=> (div_self hj.ne').symm)
          simpa using! OPE.Columns.fare_rate (v:=fun j=>j) (d:=d) (e:=i) hX.toTableTickets tendsto_id C.S.divergent hz
       refine ⟨fun i=> ‖u‖*r i,fun i=> mul_nonneg (norm_nonneg _) (OPE.Columns.fare_pos ..|>.le), by simpa only [zero_add] using (RateLE.const ‖u‖ C.S.divergent).mul (hr.pays C.S.divergent),fun k hk x=>?_⟩
       let a:= chargeTerm d x (Q k); change ‖u x‖≤‖u‖*r k*a
       have hp := tallyRange T M h hk (fun _=>x) x tendsto_const_nhds
       let z (t:ℝ):= ‖u‖ * r k*t
       have hx(t:ℝ)(he:a<t): ‖u x‖≤z t:=by
           obtain ⟨y,⟨w,hw⟩,hy⟩:= OPE.Columns.limit_cap hX.toTableTickets κ.simpleGate hB pi (show i<d by omega) (fun _=>x) x h hk (hp.eventually (ge_mem_nhds he)) tendsto_const_nhds
           have hz' : u x=u (x-y) := by rw [_root_.map_sub,show u y=0 by change v (W.project d y)=0; rw [← hw]; exact hV _ (lt_add_one _) _ _,sub_zero]
           rw [hz']; apply (u.le_opNorm _).trans; exact (mul_le_mul_of_nonneg_left hy (norm_nonneg _)).trans_eq (by unfold z r; ring)
       exact ge_of_tendsto (show Tendsto z (𝓝[>] a) (𝓝 (z a)) from (continuous_const.mul continuous_id|>.continuousWithinAt)) (show ∀ᶠ i in 𝓝[>] a, ‖u x‖ ≤ z i from (show ∀ᶠ i:ℝ in 𝓝[>] a,a < i from self_mem_nhdsWithin).mono fun i hi=> hx i hi)
-- issue uniform rate over M/h? highBill doesn't require uniform rates.
end YM.OPE.Lake
