import YM.Integration.FVA1Physical.Wilson.ResetEnvelope
import YM.Integration.FVA1Physical.Wilson.ComposedDegree
import YM.Integration.FVA1Physical.Sources.Round2.FieldMasks

/-! All scalar input prices for the marked observable's full finite-order
change of coupling are supplied by the true successive inverse temperatures
and the independent formal kinetic jet on that very realized scene. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Bout MSbar.Duel MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.CrossH MSbar.Measuring
open PhysicalNext.Repeat.Legato Push.Uniform MSbar.Midpoint MSbar.Bakery MSbar.Bakery.Portal MSbar.Bakery.Film
open Extra.Iteration Push.PriceCompiler PhysicalNext.Repeat.Roost Next.Foundations
open RGComparison.Core16.Spool RGComparison.Core16.Lumen YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology BigOperators
variable {G:Gauge}

private theorem true_ratio_band {y z b f : ℝ} (yb : y/2 ≤ b) (by' : b ≤ 2*y)
    (zf : z/2 ≤ f) (fz : f ≤ 2*z) (yz : y ≤ z) (zy : z ≤ 2*y) (pos : 0 < y) :
    1/4 ≤ cue b/cue f ∧ cue b/cue f ≤ 4 := by
  have bz := (half_pos pos).trans_le yb
  have fp := (half_pos (pos.trans_le yz)).trans_le zf
  have pb := Real.sqrt_pos.mpr bz
  have pp := Real.sqrt_pos.mpr fp
  have sb := Real.sq_sqrt bz.le
  have sf := Real.sq_sqrt fp.le
  unfold cue
  rw [inv_div_inv]
  constructor
  · apply (le_div_iff₀ pb).mpr
    nlinarith only [sb,sf,pb,pp,yb,by',zf,yz,sq_nonneg (Real.sqrt b-4*Real.sqrt f)]
  · apply (div_le_iff₀ pb).mpr
    nlinarith only [sb,sf,pb,pp,yb,fz,zy,sq_nonneg (Real.sqrt f-4*Real.sqrt b)]

theorem measured_source_on (simple : G.Simple) (R : PhysicalNext.Repeat.Legato.Run G)
    (u : G.ColorIndex) (V : Voice G) (inv : Qlocal.Schedule.vacuumInvoice u V R.metals R.rolls R.alloy R.kit)
    (p r s h m : ℕ) (hr : p+2 ≤ r) (hs : 6 ≤ s) {η:ℝ} (ηpos : 0<η) (ηsmall : η<(p:ℝ)+1) :
    ∀ᶠ k:ℕ in atTop,∀ N n, k ≤ N →
      ∀ (S:Scene R.family.path.levels n r), Realized R.alloy.B.kin N n k r (Lis.sun G u) S →
      ∀ j, k ≤ j → j<N →
        let y:=R.family.path.levels.clock.hatBeta j
        let t:=cue (R.family.path.rep N n j).beta
        let v:=t/cue (R.family.path.rep N n (j+1)).beta
        ∀ (τ:Type) [Fintype τ] [DecidableEq τ] (c:Side) (l:τ→Site c) (W:Finset (Site c))
          (a:ℝ) (T:PowerSeries (Pot τ)),
          (∀ i ≤ p,Vault l W a s h 0 (PowerSeries.coeff i T) (y^(η/16))) →
          Vault l W a s h 0 (scalarResetRow m p (S.action j) t v T) (t^((p:ℝ)+1-η)) := by
  have receipt := (Qlocal.Schedule.docket_of_invoice simple R u V inv).1
  have growth:Tendsto (fun j=>(R.alloy.B.a.params j).order) atTop atTop:=by
    apply tendsto_atTop.2;intro i
    filter_upwards [eventually_ge_atTop (R.t i)] with j ready
    exact (Nat.le_succ i).trans (((R.makes.stages i).2 j ready).1)
  have ch := (R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  have estate := inv.1 growth
  have merit := townsR R.b R.Q R.T R.t R.stories R.doors ch
  let A:=R.family.path.levels
  have rise:=RG01.Physical.hats simple A
  obtain ⟨K,all⟩ := eventually_atTop.mp (rise.eventually (measured_source_envelope s h m p r hr ηpos ηsmall))
  obtain ⟨K₁,ad⟩ := eventually_atTop.mp (RG01.Physical.nextHat simple A)
  obtain ⟨K₂,large⟩ := eventually_atTop.mp (rise.eventually_ge_atTop 2)
  filter_upwards [receipt.purse s r (r+4) hs (by omega) (by omega),
    Alto.skyline R.alloy.B r simple estate.levy merit s u hs,eventually_ge_atTop K,eventually_ge_atTop K₁,
    eventually_ge_atTop K₂] with k docket bank delay d₁ d₂
  intro N n kn S scene j kj jN y t v τ _ _ c l W a T input
  have paid := (docket N n kn).2 S scene
  have tilt := (bank N n S scene).2 j kj jN
  obtain ⟨_,_,unit,_,_⟩ := scene.step j jN kj
  let f:=(R.family.path.rep N n (j+1)).beta
  let b:=(R.family.path.rep N n j).beta
  let z:=A.clock.hatBeta (j+1)
  have high:2 ≤ y:=large j (d₂.trans kj)
  have yz:y ≤ z:=by
    dsimp only [y,z]
    rw [←Next.Scheduling.Deployment.hat (a:=A) j]
    exact le_add_of_nonneg_right (mul_nonneg (Gauge.slopeConstant_pos simple).le
      (Real.log_nonneg (Nat.one_le_cast.mpr (A.S.block j).property)))
  have s₁ := (R.makes.wilson.represents N n j jN.le).band
  have s₂ := (R.makes.wilson.represents N n (j+1) jN).band
  have s0 : 0 < y:=by linarith only [high]
  have upper := ad j (d₁.trans kj)
  have ratio := true_ratio_band (b:=b) (f:=f) s₁.1 s₁.2 s₂.1 s₂.2 yz upper s0
  have good : 1 ≤ b:=by have h:y/2 ≤ b:=s₁.1; linarith only [high,h]
  have t1 : t ≤ 1 := inv_le_one_of_one_le₀ (by simpa using Real.sqrt_le_sqrt good)
  exact all j (delay.trans kj) τ c l W a t v (S.action j) T (Mosaic.ever s0 s₁.1 s₁.2)
    t1 ratio.1 ratio.2 unit tilt (paid.2.1 j kj jN) input

end YM.Integration.FVA1Physical.Wilson
