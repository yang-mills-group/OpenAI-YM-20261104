import YangMills.WilsonProof.NativeSupport.Commissioned259.Horizon.Arrangements
/-!
# Apply readout rotation and tint average to the *older* estimates: G.5

Proof of `bridge_averaged`, `fresh_bridge` of `OPE/Orbits/Fee.lean`, modified
for genuine *logarithmic* rate accounts as requested (not the RateLE estimates).
Using the actual Haar choice on its compact geometry and ALL those bearing support
choices, unaltered during operations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flash259HorizonFork
open Function Filter Set Asymptotics MeasureTheory Table Extraction Spec Arboreal OPE.Orbits
open scoped Topology Classical BigOperators
open Node Log
attribute [local instance] YM.Work.A15.compact_ortho Orbits.measO Orbits.borelO Orbits.hμ
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {I J : Type}[Fintype I] {d:I→ℕ}{M δ:ℝ} (mn:0≤M)(dp:0<δ)
    {l:Filter J}{r:J→ℝ}{x:J→ I→E4}{o:J→E4}
    (H:SingleLog F Q.port) (u:Labels S d) (h k:ℕ)
    (hr:Tendsto r l (𝓝[>] 0)) (hx:∀ᶠ i in l, WithinRoom (r i) M δ (x i) (o i))
local notation "charge" k:max => fun i:J=> r i^k/r i^(∑ i,d i)
local notation "ρ" => F.room.kernel.spin
local notation "X" => F.sector.turns
local notation "Z" u:max => fun i:J=> shadowOld Q.port h (x i) (o i) u

include hr hx H mn dp
lemma receipt (w:Labels S d) (v:J→ S.Field h) (t:J→Ortho)
    (budget:∀ a:Exterior C.book, Allowance l r (charge (h+1)) (fun i=> discrepancy S h (x i) (o i) w (v i) (swung a (t i) (o i)) (turnsPort X (t i) a))) :
    Allowance l r (charge (h+1)) (fun i=> spinning Q.port X k (x i) (o i) (t i) w-
        spinning Q.port X k (sole (o i)) (o i) (t i) (d:=fun (_:Unit)=>h) (sole (v i))) := by
  let U (j:Mode F.sector.derivatives) i:= ∑ a∈(Q.port.sheet j).support,
      ((Q.port.sheet j) a * discrepancy S h (x i) (o i) w (v i) (swung a (t i) (o i)) (turnsPort X (t i) a)) •
        F.sector.turns.act k (t i) (Q.port.loaded j k)
  refine (Allowance.sum hr (bands F.sector.derivatives k) U (fun j hj=>?_)).congr ((margin F mn dp H hr hx k).mono fun i h=>?_)
  · refine Allowance.sum hr _ _ fun a ha=>?_; refine (Allowance.smul (Allowance.mul (Allowance.fixed _) (budget a)) (Allowance.covers (landed t _ (Q.law.spin k (Q.port.loaded j k))))).extend ?_
    exact Eventually.of_forall fun i=>by simp
  dsimp only; symm; rw [discrepancy_spin Q.port Q.law Q.continuum F.phase.transport.motion w (v i) h]; exact Finset.sum_congr rfl (fun i hi=> Finset.sum_smul)

omit mn dp H hr hx
private lemma cell_margin (v:E4):orbitMargin Q.port k (sole v) v :=by
    convert (translateMargin k (sole 0) 0 v).mpr (centerMargin Q.port k)
    · exact (zero_add v).symm
    exact (zero_add ..).symm
private lemma int_live {q:I→E4}{z:E4}{n:ℕ} (w:Labels S d)(hx:orbitMargin Q.port n q z):Integrable (fun k=>spinning Q.port X n q z k w) haar:=by
    let f i:=bears X Q.port i n q z w; refine Integrable.congr (f:=fun j=>∑ i∈bands F.sector.derivatives n,f i j) ?_ (Eventually.of_forall (fun i=> (Orbits.scatter Q.port Q.continuum n q z w i).symm)); exact integrable_finsetSum (bands F.sector.derivatives n) (μ:=haar) (f:=f) fun i hi=>integrable_bears Q.port Q.law Q.continuum n q z i w (hx i hi)

include mn dp H hr hx
lemma averaged (w:Labels S d)(v:J→S.Field h)
    (budget : Allowance (l ×ˢ (⊤ : Filter Ortho)) (r ∘ Prod.fst) ((charge (h+1)) ∘ Prod.fst) (fun i=>
      spinning Q.port X k (x i.1) (o i.1) i.2 w-spinning Q.port X k (sole (o i.1)) (o i.1) i.2 (d:=fun (_:Unit)=>h) (sole (v i.1)))) :
    Allowance l r (charge (h+1)) (fun i=> averageV Q.port X k (x i) (o i) w-averageV Q.port X k (sole (o i)) (o i) (d:=fun (_:Unit)=>h) (sole (v i))) := by
  let E i z := spinning Q.port X k (x i) (o i) z w-spinning Q.port X k (sole (o i)) (o i) z (d:=fun (_:Unit)=>h) (sole (v i))
  let p (i:J) := (charge (h+1)) i; have e : ∀ᶠ i in l, 0 ≤ p i := (hr.eventually self_mem_nhdsWithin).mono fun i hi=>by unfold p; change 0<r i at hi; positivity
  obtain ⟨C,hC,b,B⟩:= Allowance.budget (hr.comp tendsto_fst) budget (tendsto_fst.eventually e)
  obtain ⟨U,hU,V,hV,h⟩:= Filter.eventually_prod_iff.mp B
  refine ⟨b, IsBigO.of_bound C ?_⟩
  filter_upwards [margin F mn dp H hr hx k, hU, e, log_pays hr] with i hX hU e hr
  have cap : ‖(∫ z, E i z ∂haar)‖ ≤ C*badge (r i)^b*p i := by
    let s:=C*badge (r i)^b*p i
    simpa only [ Measure.real,measure_univ,ENNReal.toReal_one,mul_one ] using (norm_integral_le_of_norm_le_const (Eventually.of_forall fun z=> show ‖E i z‖ ≤ s from h hU (Filter.eventually_top.mp hV z)) : ‖(∫ z,E i z ∂haar)‖ ≤ s * haar.real univ)
  rw [averageV,if_pos hX, averageV,if_pos (cell_margin F Q k _), ← integral_sub (int_live F Q w hX) (int_live F Q _ (cell_margin F Q k _))]; change ‖(∫ z,E i z ∂haar)‖ ≤ C*‖p i* badge (r i)^b‖
  exact cap.trans_eq (by rw [Real.norm_of_nonneg (by positivity)]; ring)

set_option maxHeartbeats 800000 in
lemma G5 (u:Labels S d) : Allowance l r (charge (h+1)) (fun i=> Q.fresh k (x i) (o i) u-Q.cutTest k h ((Z u) i)) := by
  have v:=tendsto_fst (f:=l) (g:= (⊤:Filter Ortho)); let z := fun i:J=> S.conj ρ h ((Z u) i)
  have vals (b:Exterior C.book) := evaluations F mn dp H u h (hr.comp v) (x:=x ∘ Prod.fst) (o:=o ∘ Prod.fst) (v.eventually hx) Q.law b Prod.snd
  have hh1:= averaged F Q mn dp H h k hr hx u (Z u) (receipt F Q mn dp H (x:=x ∘ Prod.fst) (o:=o ∘ Prod.fst) h k (hr.comp v) (v.eventually hx) u ((Z u) ∘ Prod.fst) Prod.snd fun a=> (vals a).1)
  have hh2:= averaged F Q mn dp H h k hr hx (bar ρ u) z (receipt F Q mn dp H (x:=x ∘ Prod.fst) (o:=o ∘ Prod.fst) h k (hr.comp v) (v.eventually hx) (bar ρ u) (z ∘ Prod.fst) Prod.snd fun a=> (vals a).2)
  -- check real & tint; differentiate only elsewhere
  have E(i:J) : checkReal Q.port Q.law Q.continuum k (x i) (o i) u- checkReal Q.port Q.law Q.continuum k (sole (o i)) (o i) (d:=fun (_:Unit)=>h) (sole ((Z u) i)) =
      (2:ℝ)⁻¹ • ((averageV Q.port X k (x i) (o i) u-averageV Q.port X k (sole (o i)) (o i) (d:=fun (_:Unit)=>h) (sole ((Z u) i))) +
      (conjugateR ρ k) (averageV Q.port X k (x i) (o i) (bar ρ u)-averageV Q.port X k (sole (o i)) (o i) (d:=fun (_:Unit)=>h) (sole (z i)))) := by
    rw [checkValue,checkValue,map_sub]; change _ = (2:ℝ)⁻¹ • (_ +(S.conj ρ k _ - S.conj ρ k _)); rw [←smul_sub]; apply congr_arg; unfold z; abel
  have it(i:J) : checkReal Q.port Q.law Q.continuum k (sole (0:E4)) (0:E4) (d:=fun (_:Unit)=>h) (sole ((Z u) i)) = checkReal Q.port Q.law Q.continuum k (sole (o i)) (o i) (d:=fun (_:Unit)=>h) (sole ((Z u) i)) := by
    symm; apply Eq.trans ?_ (checkReal_transfer k Q.law Q.continuum _ _ _ (o i)); rw [zero_add,(show (fun q:Unit=>sole (0:E4) q+o i)=sole (o i) from funext fun _=>zero_add _)]
  have i (i:J) : Q.fresh k (x i) (o i) u-Q.cutTest k h ((Z u) i)= Q.knife k (checkReal Q.port Q.law Q.continuum k (x i) (o i) u-
      checkReal Q.port Q.law Q.continuum k (sole (o i)) (o i) (d:=fun (_:Unit)=>h) (sole ((Z u) i))) := by
    rw [Reader.fresh_eq, ← Q.single, Reader.fresh_eq,map_sub,it]
  simp_rw [i,E]
  refine ((Allowance.linear (LinearMap.toContinuousLinearMap (Q.knife k)) (Allowance.smul (Allowance.fixed ((2:ℝ)⁻¹)) (Allowance.add hr hh1 (Allowance.linear (LinearMap.toContinuousLinearMap (conjugateR ρ k)) hh2))))).extend ?_
  exact Eventually.of_forall fun i=>one_mul _
end YM.OPE.Flash259HorizonFork
