import YangMills.WilsonProof.NativeSupport.Commissioned259.Horizon.Modernist
/-! # Horizon-compatible prices for substitution. Towards G.5, G.7 first part (actually on `fresh` layer,
all channels), G.8. Genuine polylog estimates for the physical application. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flash259HorizonFork
open Function Filter Set Asymptotics MeasureTheory Table Extraction Spec Arboreal OPE.Orbits
open scoped Topology Classical BigOperators
open Node Log
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {I J : Type}[Fintype I] {d:I→ℕ}{M δ:ℝ} (mn:0≤M)(dp:0<δ)
    {l:Filter J}{r:J→ℝ}{x:J→ I→E4}{o:J→E4}
    (H:SingleLog F Q.port) (u:Labels S d) (h k:ℕ)
    (hr:Tendsto r l (𝓝[>] 0)) (hx:∀ᶠ i in l, WithinRoom (r i) M δ (x i) (o i))
local notation "ρ" => F.room.kernel.spin
local notation "Z" => fun h:ℕ=> fun i:J=> shadowOld Q.port h (x i) (o i) u
local notation "charge" h:max => fun i:J=> r i^h/r i^(∑ i,d i)
include hr hx H mn dp
lemma costs (w:Mode F.sector.derivatives) : Allowance l r (charge w.1) (fun i=> Q.port.ope w (x i) (Orbits.names u) (o i)) := by
  obtain ⟨k,H⟩:= H.terms I (Orbits.names u) δ M dp mn w
  refine ⟨k,IsBigO.of_bound' ?_⟩; filter_upwards [hr.eventually H,log_pays hr,hx,hr.eventually self_mem_nhdsWithin] with i V h j u
  exact ((V _ _ j).2).trans_eq (by rw [Real.norm_of_nonneg (by change 0 < r i at u; positivity)]; exact mul_comm ..)
lemma basis_amount : Allowance l r (charge k) (fun i=> Q.fresh k (x i) (o i) u) := by
  have H := G5 F Q mn dp H k k hr hx u
  have p : ∀ᶠ i in l,0 < r i ∧ r i ≤ 1 := hr.eventually ( (show ∀ᶠ i : ℝ in 𝓝[>]0, 0 < i from self_mem_nhdsWithin).and (eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds zero_lt_one)))
  let A i:= Q.cutTest k k (Z k i)
  have u' : Allowance l r (charge k) A := by
    simp_rw [A,shadowOld, shadow,map_sum,map_smul]; refine Allowance.sum hr _ _ fun j h=>?_
    have e : j.1 ≤ k := (full_bands ..).mp h
    rcases e.lt_or_eq with e|e
    · simp_rw [(Q.port).cost j h,Q.cut_rise,Q.kills_lower _ _ e, smul_zero]; exact Allowance.zero _
    exact (Allowance.smul (costs F Q mn dp (show SingleLog F Q.port from by assumption) u hr hx j) (Allowance.fixed (Q.cutTest k k (Q.port.loaded j k)))).extend (u:=charge k) (Eventually.of_forall fun i=>by simp only [e,mul_one])
  refine (Allowance.add hr (H.transport (IsBigO.of_bound' ?_)) u').congr (Eventually.of_forall fun i=> sub_add_cancel ..)
  filter_upwards [p] with i ⟨q,e⟩; simp only [norm_div,norm_pow,Real.norm_of_nonneg q.le]; exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (pow_nonneg q.le k) e) (pow_nonneg q.le _)
lemma horizon_packet : Allowance l r (charge (h+1)) (fun i=> Q.packet h (x i) u (o i)-Z h i) := by
  let v (j:Fin (h+1)) i:= Q.fresh j.val (x i) (o i) u-Q.cutTest j.val h (Z h i)
  let V:=F.sector.derivatives
  refine Allowance.congr (Allowance.sum hr Finset.univ (fun j:Fin (h+1)=> (fun i=> V.rise (Nat.le_of_lt_succ j.isLt) (v j i)))
    (fun j _=> Allowance.linear (LinearMap.toContinuousLinearMap (V.rise (Nat.le_of_lt_succ j.isLt))) (G5 F Q mn dp H h j hr hx u))) (Eventually.of_forall fun i=>?_)
  have he:= Q.reconstruct h h le_rfl (Z h i); rw [F.sector.derivatives.arrival Q.continuum.laws.toSymmetric Q.lifts] at he
  unfold v; simp_rw [map_sub]; rw [Finset.sum_sub_distrib]; exact congr_arg (_-·) he
omit hr hx

-- `orbit-safe` eventually from `WithinRoom`. Here useful to display the implied estimates
-- in exactly G.5 and G.8 currency and unbundled widths in the interfaces.
lemma budget_fixed (u:Labels S d) : ∃ (B:ℝ),0 < B ∧ ∃ n:ℕ, ∀ᶠ r in 𝓝[>] (0:ℝ),
    ∀ x o, WithinRoom r M δ x o → r^(∑ i,d i)*(
      ‖Q.fresh k x o u-Q.cutTest k h (shadowOld Q.port h x o u)‖+‖Q.packet h x u o-shadowOld Q.port h x o u‖)
        ≤ B*badge r^n*r^(h+1) := by
  let I':={i:ℝ × (I→E4) × E4 // WithinRoom i.1 M δ i.2.1 i.2.2}
  let r(i:I'):=i.val.1; let x(i:I'):=i.val.2.1; let o(i:I'):=i.val.2.2; let X:=comap r (𝓝[>] 0)
  have hx : ∀ᶠ i in X, WithinRoom (r i) M δ (x i) (o i) := Eventually.of_forall Subtype.property
  have q : Tendsto r X (𝓝[>] 0) := tendsto_comap
  obtain ⟨C,hC,n,K⟩:= Allowance.budget q (Allowance.add q (G5 F Q mn dp H h k q hx u|>.norm) (horizon_packet F Q mn dp H u h q hx|>.norm)) ( (q.eventually self_mem_nhdsWithin).mono fun i hi=>by change 0 < r i at hi; positivity)
  refine ⟨C,hC,n,?_⟩; filter_upwards [eventually_comap.mp K,self_mem_nhdsWithin] with r ht hr x o live
  have e:= ht (⟨(r,x,o),live⟩:I') rfl; let z:= ‖Q.fresh k x o u-Q.cutTest k h (shadowOld Q.port h x o u)‖+‖Q.packet h x u o-shadowOld Q.port h x o u‖
  let c:=∑ i,d i; change ‖z‖≤ C*badge r^n*(r^(h+1)/r^c) at e; change r^c*z ≤ _; rw [Real.norm_of_nonneg (show 0 ≤ z by unfold z; positivity),← mul_div_assoc] at e; rw [mul_comm]; exact (le_div_iff₀ (pow_pos hr c)).mp e
end YM.OPE.Flash259HorizonFork
