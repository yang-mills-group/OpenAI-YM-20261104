import YM.Integration.WilsonSeparatedTubeEnvelope

/-! The sign-sensitive position detector uses the genuine exterior at its own
radius. This tube estimate keeps the individual measured physical costs before
choosing the interpolation order or the real Euclidean center. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkTubeFee
open Function Filter Set Metric Extraction Spec Trace Trace.Pilot TraceExtension Climb
open Boundary Boundary.Surface GapsContact GapsContact.Ascent GapsContact.Tunnel EveryPhase
open WilsonSeparatedTubeEnvelope
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel C.book).Hierarchy}{Z:Trace.Terrace.Arch C}

theorem original (hG:G.Simple)(bliss:Bliss F l Z H)(L:Almanac F){n:ℕ}(d:Fin n→ℕ):
    ∃A:ℝ,0≤A ∧ ∃p:ℕ,∀ᶠr in trail,∀(σ:Equiv.Perm (Fin n))(u:∀i,S.Field (d (σ i)))
      (i:Survey F)(D:∀k,Blanket k)(X:(Survey.reads L i).world.Aurora D),
      AnalyticOnNhd ℂ (weather X (tag u) r) (tube n) ∧ ∀δ∈Ioc (0:ℝ) 1,
      ∀x:Full n,Room (shade x) δ → ‖weather X (tag u) r x‖ ≤
        A*(LogV r/δ)^p*∏j,Ascent.cost F (d (σ j)) r (u j):=by
  choose roof a m hroof ha sky using fun i=>Ascent.opened_sky F hG bliss (d i)
  let rate (i:Fin n):=a i^2*(8:ℝ)^(2*m i)
  refine ⟨∏i,rate i,Finset.prod_nonneg fun i _=>by dsimp only [rate];positivity,∑i,2*m i,?_⟩
  have roofs:∀ᶠr in trail,∀i,r≤roof i:=eventually_all.mpr fun i=>(ge_mem_nhds (hroof i)).filter_mono nhdsWithin_le_nhds
  filter_upwards [roofs,self_mem_nhdsWithin (a:=0),(ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds]
    with r hroof hr hu
  intro σ u i D X
  refine ⟨hollow X (observe L i X).2 _ r hr,?_⟩
  intro δ hd x hx
  have scal:Room (shade ((r:ℂ) • x)) (r*δ):=by
    rw [←valley x,←glow_scales,im_glow];exact hx.mul hr.le
  have price:=enough_fields L i X (d:=fun j=>d (σ j)) u ⟨hr,hu⟩ hd
    (R:=fun j=>roof (σ j)) (A:=fun j=>a (σ j)) (m:=fun j=>m (σ j))
    (fun j=>sky (σ j)) (fun j=>hroof (σ j)) _ scal
  apply price.trans_eq
  let t:=LogV r/δ
  calc
    ∏j:Fin n,a (σ j)^2*(8*t)^(2*m (σ j))*Ascent.cost F (d (σ j)) r (u j)
        = ∏j:Fin n,(rate (σ j)*t^(2*m (σ j)))*Ascent.cost F (d (σ j)) r (u j):=by
          apply Finset.prod_congr rfl;intro j _;dsimp [rate];rw [mul_pow];ring
    _=(∏j:Fin n,rate j*t^(2*m j))*∏j,Ascent.cost F (d (σ j)) r (u j):=by
      rw [Finset.prod_mul_distrib,Equiv.prod_comp σ (fun j=>rate j*t^(2*m j))]
    _=_:=by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]

end YM.Integration.WilsonMovingForkTubeFee
