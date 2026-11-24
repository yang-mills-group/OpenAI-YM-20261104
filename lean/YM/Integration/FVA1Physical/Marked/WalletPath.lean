import YM.Integration.FVA1Physical.Marked.Purchased
import YM.Integration.FVA1Physical.Sources.Round2.ConditionalFields
import YM.Integration.FVA1Physical.ExceptionalMass

/-! Carry the complete M7a wallet to the independent physical moments.
A discrepancy at the bare level is transported as one signed marked density;
the history never factorizes conditionally correlated source modes. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Qlocal.Actual.Season.Studio
open Lattice RG Wilson Tree Marker Extra.Trajectories RG3.Script.Picnic MeasureTheory
open Pressure ConnectedActivityE6
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open Qlocal.Quipu Quipu.Sonnet Tern Parabola Moonset Rooms
open Integration FVA1Physical FVA1Physical.Round2 MergeProof.Accent LocalLTE.Sail
open scoped Classical BigOperators

variable {I Ω : Type} [Fintype I] [DecidableEq I]
    {G : Gauge} {B : Census I} (X : Run G) {N n z m j b qd : ℕ}
    {ξ : I→ℕ} {ζ : ℕ→ℝ} {K : ℕ→ℕ} {T : Ray B} {δ d : ℝ}
    {x : (i : ℕ) → Rep G (X.alloy.B.a.S.side i n)}
    {o : (i : ℕ) → I→Site (X.family.side i n)}
    {U : (i : ℕ) → Wallet Ω (o i) (x i) B ξ qd b}

theorem Delivered.full_path (h : Delivered X ζ K ξ b T o d U z (N:=N) (j:=j) (δ:=δ))
    (_hz : z ≤ m) (hi : m ≤ j) (t : Ω) :
    (interpretation (N:=N) X ξ b m (U m)) t = gust X.family.path N n j ((interpretation (N:=N) X ξ b j (U j)) t) m hi := by
  induction hi using Nat.decreasingInduction with
  | self => exact (gust_base ..).symm
  | of_succ s hs ih =>
    rw [gust_step _ _ _ _ _ hs]
    exact (congrFun (h.footprint s _hz hs) t).trans
      (congrArg ((X.family.path.levels.clock.op s n).push (X.family.path.β N n (s+1))) (ih (_hz.trans (Nat.le_succ _))))

private theorem gust_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : History G) (N p j : ℕ) (u v : Config G (A.S.side j p)→E)
    (hu : Integrable u (prior G _)) (hv : Integrable v (prior G _)) (k : ℕ) (hk : k ≤ j) :
    gust A N p j (u-v) k hk = gust A N p j u k hk - gust A N p j v k hk := by
  induction hk using Nat.decreasingInduction with
  | self => rw [gust_base,gust_base,gust_base]
  | of_succ i h ih =>
    rw [gust_step _ _ _ _ _ h,gust_step _ _ _ _ u h,gust_step _ _ _ _ v h,ih]
    funext W
    simp only [Pi.sub_apply,StepData.push,smul_sub]
    exact integral_sub (StepData.push_slice (A.levels.transition_mass ..) W _ (gust_live _ _ _ _ _ hu h))
      (StepData.push_slice (A.levels.transition_mass ..) W _ (gust_live _ _ _ _ _ hv h))

/-- Exact signed mismatch between the entire actual marked wallet and the
physical joint moment table, including all higher cumulants and failed rows.
The only source of the mismatch is its *bare* full marked density. -/
theorem Delivered.mixed_source_origin (Y : Batch X.family.path N n I) (t : Ω) (h : Delivered X ζ K ξ b T o d U z (N:=N) (j:=N) (δ:=δ))
    (_hz : z ≤ m) (hi : m ≤ N)
    (_integrable : Integrable ((interpretation (N:=N) X ξ b N (U N)) t) (prior G _)) (v : Config G (X.family.side m n)) :
    let vacuum := ((X.family.path.rep N n m).eval v:ℂ)⁻¹
    vacuum • (interpretation (N:=N) X ξ b m (U m)) t v - momentTable B Y m hi v =
      vacuum • gust X.family.path N n N (fun w => interpretation (N:=N) X ξ b N (U N) t w - Y.raw B w) m hi v := by
  intro vacuum
  rw [h.full_path X _hz hi t,← physical_moment_table (H:=X.family.path) X.makes.wilson B Y m hi v,
    ←smul_sub]
  congr 1
  exact (congrFun (gust_sub X.family.path N n N ((interpretation (N:=N) X ξ b N (U N)) t) (Y.raw B) _integrable (Bandage.Harmonics.physicalSeed_integrable X.family.path X.makes.wilson B Y) m hi) v).symm

/-- Any uniform error in the complete normalized bare density propagates to
every retained field and all later scales with coefficient one. -/
theorem Delivered.mixed_source_price (Y : Batch X.family.path N n I) (t : Ω) (h : Delivered X ζ K ξ b T o d U z (N:=N) (j:=N) (δ:=δ))
    (_hz : z ≤ m) (hi : m ≤ N) (v : Config G (X.family.side m n))
    (_integrable : Integrable ((interpretation (N:=N) X ξ b N (U N)) t) (prior G _)) (e : ℝ)
    (_seed : ∀ u, ‖((X.family.path.rep N n N).eval u)⁻¹ • ((interpretation (N:=N) X ξ b N (U N)) t u - Y.raw B u)‖ ≤ e) :
    ‖(((X.family.path.rep N n m).eval v : ℂ)⁻¹) • (interpretation (N:=N) X ξ b m (U m)) t v - momentTable B Y m hi v‖ ≤ e := by
  rw [h.mixed_source_origin X Y t _hz hi _integrable v,← Complex.ofReal_inv]
  change ‖((X.family.path.rep N n m).eval v)⁻¹ • gust X.family.path N n N (fun w => interpretation (N:=N) X ξ b N (U N) t w - Y.raw B w) m hi v‖ ≤ e
  exact gust_vacuum_bound X.family.path X.makes.wilson N n _ e _seed m hi v

/-- The matched case requires only identification of the real wallet's
rendered logarithm with the prescribed physical singleton sum on the bare mesh.
No inherited source comparison, regularity or integrability invoice. -/
theorem Delivered.mixed_source_eq (Y : Batch X.family.path N n I) (t : Ω) (h : Delivered X ζ K ξ b T o d U z (N:=N) (j:=N) (δ:=δ))
    (_hz : z ≤ m) (hi : m ≤ N) (v : Config G (X.family.side m n))
    (_born : ∀ u, (interpretation (N:=N) X ξ b N (U N)) t u =
      Poly.pass ((U N).render (Stores.till (X.alloy.B.a.clock.hatBeta N))
        (Coat.gStep (X.family.path.β N n N)) t u) * Poly.bead B (((X.family.path.rep N n N).eval u) : ℂ))
    (_initial : ∀ u, (U N).render (Stores.till (X.alloy.B.a.clock.hatBeta N))
        (Coat.gStep (X.family.path.β N n N)) t u = Mach B (fun i=>Y.wavelengths i u)) :
    (((X.family.path.rep N n m).eval v : ℂ)⁻¹) • (interpretation (N:=N) X ξ b m (U m)) t v = momentTable B Y m hi v := by
  have raw : (interpretation (N:=N) X ξ b N (U N)) t = Y.raw B := by
    funext u
    rw [_born u,_initial u,mul_comm,Poly.product_bead]
    rfl
  rw [h.full_path X _hz hi t,raw]
  exact physical_moment_table (H:=X.family.path) X.makes.wilson B Y m hi v
end YM.Qlocal.Actual.Season.Studio
