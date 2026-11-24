import YM.Integration.WilsonPhysicalAbsoluteVaneDirections

/-! On the actual homogeneous public chart, the compensated original signed coordinate
read tends to its prescribed corrected free field on the incumbent weak book. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalAbsoluteVaneHome
open Function Filter Spec Table Climb PhysMS PhysMS.Frame Trace.Pilot Trace.Target
open PhysicalNext.Repeat.Legato Further.CorrectedLift
open OPE Next.Extract RG.Supply MS MS.Land FVA2 FVA2.Register
open WilsonPhysicalAllGradeWeakElection WilsonPhysicalWeakWallStaff WilsonPhysicalWeakSameStation WilsonPhysicalWeakWallBooks
open WilsonPhysicalWeakWallBounded (cost)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonPhysicalAbsoluteVaneDirections (native variation)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
variable (F:Final R.family f S)(J:ℝ→tower S){H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}
  (simple:G.Simple)(a:Assignment F J H l simple){D T:ℕ}{δ:ℝ}
  (books:(r:{r:ℝ//0<r ∧ r<δ})→ Book F (l:=l) H arch D T r.val)
  (shared:∀r,∃cap:D≤(a.day r.val).1,Shared F (books r) (trim cap (a.day r.val).2))

variable (Z:WilsonPrescription G)(lead:PhysMS.Leading F J)(obeys:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)
variable {ι:Type*}(u:Filter ι)(age:ι→{r:ℝ//0<r ∧ r<δ})(near:Tendsto (fun i=>(age i).val) u trail)

def read {r:ℝ}(B:Book F (l:=l) H arch D T r)(d:Fin (D+1))(N p:ℕ):(Bel R.family.book).Field d →ₗ[ℂ] R.family.label d where
  toFun v:=native F B d N p ((B.V d).symm (WilsonPositionHomogeneousFrame.homogeneous F J Z r d v))
  map_add' x y:=by simp [WilsonPhysicalAbsoluteVaneDirections.native,Finset.sum_add_distrib,add_smul]
  map_smul' c x:=by simp [WilsonPhysicalAbsoluteVaneDirections.native,Finset.smul_sum,smul_smul]

theorem continuity (d:Fin (D+1)):Continuous (variation (R:=R) d):=by
  unfold variation
  fun_prop

include shared near lead obeys in
theorem fixed (d:Fin (D+1))(v:(Bel R.family.book).Field d)(ε:ℝ)(ep:0<ε):
    ∀ᶠi in u,∀N p,(books (age i)).W.k<N →
      ‖read F J Z (books (age i)) d N p v-ladder R.family d v‖≤ε:=by
  let L:=ladder R.family d
  let x(i:ι):=((books (age i)).V d).symm (WilsonPositionHomogeneousFrame.homogeneous F J Z (age i).val d v)
  have home:Tendsto x u (𝓝 v):=WilsonPhysicalWeakHomogeneousHome.direction F J simple a books shared Z lead obeys u age near d v
  let M:=max 0 (variation (R:=R) d v)+1
  have mp:0<M:=by dsimp [M];positivity
  have budget:∀ᶠi in u,variation (R:=R) d (x i)≤M:=by
    have arrival: Tendsto (fun i=>variation (R:=R) d (x i)) u (𝓝 (variation (R:=R) d v)):=
      (continuity d).continuousAt.tendsto.comp home
    exact (arrival.eventually_lt_const (lt_add_of_le_of_pos (le_max_right _ _) zero_lt_one)).mono fun _ h=>h.le
  let η:=ε/(4*M)
  have ηp:0<η:=div_pos ep (by positivity)
  have landed:Tendsto (fun i=>L (x i)) u (𝓝 (L v)):=L.continuous.continuousAt.tendsto.comp home
  filter_upwards [WilsonPhysicalAbsoluteVaneDirections.original F J simple a books shared u age near η ηp,budget,
    Metric.tendsto_nhds.mp landed (ε/2) (half_pos ep)] with i spent cap close N p room
  have test:=spent d N p room (x i)
  have move:‖L (x i)-L v‖≤ε/2:=by rw [dist_eq_norm] at close;exact close.le
  calc
    _≤‖native F (books (age i)) d N p (x i)-L (x i)‖+‖L (x i)-L v‖:=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤2*η*M+ε/2:=add_le_add ((Push.Local.norm_le_size _ _).trans (test.trans
      (mul_le_mul_of_nonneg_left cap (by positivity)))) move
    _=ε:=by dsimp [η];field_simp;norm_num

include shared near lead obeys in
theorem original (M ε:ℝ)(hm:0≤M)(ep:0<ε):
    ∀ᶠi in u,∀d:Fin (D+1),∀N p,(books (age i)).W.k<N → ∀v:(Bel R.family.book).Field d,
      cost R.family v≤M → ‖read F J Z (books (age i)) d N p v-ladder R.family d v‖≤ε:=by
  let η:= ε/(M+1)
  have mp:0<M+1:=by linarith
  have ηp:0<η:=div_pos ep mp
  have all(d:Fin (D+1)):∀ e:Fin (Module.finrank ℂ ((Bel R.family.book).Field d)),
      ∀ᶠi in u,∀N p,(books (age i)).W.k<N →
      ‖read F J Z (books (age i)) d N p (Module.finBasis ℂ _ e)-ladder R.family d (Module.finBasis ℂ _ e)‖≤η:=
    fun e=>fixed F J simple a books shared Z lead obeys u age near d (Module.finBasis ℂ _ e) η ηp
  filter_upwards [Filter.eventually_all.mpr (fun d=>Filter.eventually_all.mpr (all d))] with i axes d N p live v cap
  let B:=Module.finBasis ℂ ((Bel R.family.book).Field d)
  let M':=read F J Z (books (age i)) d N p-(ladder R.family d).toLinearMap
  change ‖M' v‖≤ε
  rw [←B.sum_repr v,map_sum]
  calc
    _≤∑e,‖M' (B.repr v e • B e)‖:=norm_sum_le _ _
    _≤∑e,‖B.repr v e‖*η:=Finset.sum_le_sum fun e _=>by
      rw [map_smul,norm_smul]
      exact mul_le_mul_of_nonneg_left (axes d e N p live) (norm_nonneg _)
    _=(cost R.family v)*η:=by unfold cost;rw [Finset.sum_mul]
    _≤(M+1)*η:=mul_le_mul_of_nonneg_right (by linarith) ηp.le
    _=ε:=by dsimp [η];field_simp

end YM.Integration.WilsonPhysicalAbsoluteVaneHome
