import YM.Integration.WilsonThermometerWeakPairPins

/-! On a single physical frame its fixed measured packet and the raw nested readout have the same
finite-sheet readings up to the actual fixed-clearance spatial remainder. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairReader
open Function Finset Filter Set Table Extraction Spec OPE OPE.Orbits OPE.Prescription
open PhysMS PhysMS.Frame OPE.Nesting Trace Trace.Pilot
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{f:Order}{S:Table C.book}(F:Final C f S)
    {I:Type}[Fintype I]{d:I→ℕ}
    {P:Prescription F.sector.derivatives}

private lemma clearance (e:Exterior C.book):∃δ:ℝ,0<δ ∧ ClearOf 0 (bearing e) δ:=by
  have hc:=beside_distinct.mp (bearing_clear e)
  have away (i:Fin e.n):0<‖(0:E4)-bearing e i‖:=
    norm_pos_iff.mpr (sub_ne_zero.mpr (hc.2.2 () i))
  have sep(i j:Fin e.n)(h:i≠j):0<‖bearing e i-bearing e j‖:=
    norm_pos_iff.mpr (sub_ne_zero.mpr (hc.2.1.ne h))
  have lo:∀ᶠ δ in 𝓝[>] (0:ℝ),∀i:Fin e.n,δ≤‖(0:E4)-bearing e i‖:=
    eventually_all.mpr fun i=>(ge_mem_nhds (away i)).filter_mono nhdsWithin_le_nhds
  have mid:∀ᶠ δ in 𝓝[>] (0:ℝ),∀i j:Fin e.n,∀h:i≠j,δ≤‖bearing e i-bearing e j‖:=
    eventually_all.mpr fun i=>eventually_all.mpr fun j=>eventually_all.mpr fun h=>
      (ge_mem_nhds (sep i j h)).filter_mono nhdsWithin_le_nhds
  obtain ⟨δ,hp,h,hh⟩:=((show ∀ᶠ δ:ℝ in 𝓝[>]0,0<δ from self_mem_nhdsWithin).and (lo.and mid)).exists
  exact ⟨δ,hp,h,hh⟩

theorem original (hp:P.Coherent)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→tower S)(H:Leading F J)(book:Foundation F R)
    (v:(i:I)→(Climb.Bel C.book).Field (d i))(h:ℕ){M η ε:ℝ}
    (mn:0≤M)(ep:0<η)(slack:0<ε):
    ∃K:ℝ,0≤K ∧ ∀ᶠ r in trail,∀x:I→E4, WithinRoom r M η x 0 →
      ‖shadowOld P h x 0 (born J r v)-R.packet h x (born J r v) 0‖≤K*r^(h+1-ε):=by
  let K:ℝ:=∑i∈bands F.sector.derivatives h,
    (∑e∈(P.sheet i).support,‖(P.sheet i) e‖)*‖P.loaded i h‖
  refine ⟨K,by dsimp [K];positivity,?_⟩
  let A:=↥(bands F.sector.derivatives h)
  have entry (i:A)(e:↥((P.sheet i.1).support)):
      ∀ᶠ r in trail,∀x:I→E4,WithinRoom r M η x 0 → Injective (beside x (bearing e.1)) ∧
        ‖discrepancy S h x 0 (born J r v) (R.packet h x (born J r v) 0) (bearing e.1) (fields S e.1)‖≤r^(h+1-ε):=by
    obtain ⟨δ,dp,clear⟩:=clearance e.1
    have small:∀ᶠ r in trail,r<δ/(M+1):=
      (gt_mem_nhds (div_pos dp (by linarith))).filter_mono nhdsWithin_le_nhds
    filter_upwards [PhysMS.Frame.single_report F R J H book v (fields S e.1) h M η δ ε mn ep dp slack,
      small,self_mem_nhdsWithin] with r paid hr rp
    intro x hx
    have radius: M*r<δ:=by
      have h₀:=(lt_div_iff₀ (by linarith : 0<M+1)).mp hr
      nlinarith
    have joined:Injective (beside x (bearing e.1)):=by
      apply beside_distinct.mpr
      refine ⟨?_,(beside_distinct.mp (bearing_clear e.1)).2.1,?_⟩
      · intro a b eq
        by_contra ne
        have gap:=hx.spaced a b ne
        rw [eq,sub_self,norm_zero] at gap
        exact (not_lt_of_ge gap) (mul_pos ep rp)
      · intro a j eq
        have close:=hx.span a
        have far:=clear.openSpace j
        rw [eq,sub_zero] at close
        rw [zero_sub,norm_neg] at far
        linarith
    refine ⟨joined,?_⟩
    have output:=(paid x (bearing e.1) 0 hx clear).2 none
    rw [formula,← packet_read F R x 0 (born J r v) (bearing e.1) (fields S e.1) none h (bearing_clear e.1)] at output
    exact output
  filter_upwards [eventually_all.mpr (fun i:A=>eventually_all.mpr (entry i))] with r readings
  intro x hx
  apply WilsonThermometerWeakPairPins.tomography F hp
  intro i hi e he
  exact readings ⟨i,hi⟩ ⟨e,he⟩ x hx
end YM.Integration.WilsonThermometerWeakPairReader
end
