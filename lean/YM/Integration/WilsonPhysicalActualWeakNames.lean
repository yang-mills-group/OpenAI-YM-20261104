import YM.Integration.WilsonPhysicalSignedWeakSource

/-! Honest homogeneous weak fields at the original microscopic cutoff and the price of undoing their per-axis normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalActualWeakNames
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

open WilsonPhysicalSignedWeakSource (input)
open Next.Rank.Price Next.Rank.Station
open WilsonPhysicalElectedVaneHead (level)
open WilsonPhysicalStationMenuSalary (weight)

variable (d:Fin (D+1))
def name {r:ℝ}(B:Book F (l:=l) H arch D T r)(v:(Bel R.family.book).Field d)(N p:ℕ):R.family.label d:=
  (((B.rows d).arm true (WilsonPositionHomogeneousFrame.homogeneous F J Z r d v)).source (N,p))
def seed {r:ℝ}(B:Book F (l:=l) H arch D T r)(e:(R.family.labels.level d).Index)(N p:ℕ):R.family.label d:=
  (((B.rows d).arm true ((B.V d) (WilsonPhysicalVaneBasis.field R.family d e))).source (N,p))
def coefficient {r:ℝ}(B:Book F (l:=l) H arch D T r)(v:(Bel R.family.book).Field d)
    (e:(R.family.labels.level d).Index):ℂ:=(ladder R.family d (input F J Z d B v)) e

theorem entered {r:ℝ}(B:Book F (l:=l) H arch D T r)(v:(Bel R.family.book).Field d)(N p:ℕ):
    (∑e,coefficient F J Z d B v e • seed F d B e N p)=name F J Z d B v N p:=by
  let L:=B.W.wheel.atCut (N,p) (level F B d)
  have basis (e):seed F d B e N p=L (WilsonPhysicalVaneBasis.field R.family d e):=by
    rw [seed,(B.rows d).weak,LinearEquiv.symm_apply_apply]
  have original:name F J Z d B v N p=L (input F J Z d B v):=(B.rows d).weak _ _
  rw [original,←WilsonPhysicalVaneBasis.resolve R.family d (input F J Z d B v),map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [basis,map_smul]
  rfl

theorem restored {r:ℝ}(B:Book F (l:=l) H arch D T r)(v:(Bel R.family.book).Field d){N p:ℕ}(top:B.W.k≤N)
    (e:(R.family.labels.level d).Index):
    let g:=(R.family.labels.level d).grades e
    weight F B d (input F J Z d B v) N p e * WilsonPhysicalStationSignedBlock.scale R B.W N p g.1 g.2=
      coefficient F J Z d B v e:=by
  intro g
  have price:WilsonPhysicalStationSignedBlock.scale R B.W N p g.1 g.2≠0:=by
    have a:=mag_pos R.family.path.levels B.W.b B.W.k
    have b:=shrink_pos R.family R.makes top p
    unfold WilsonPhysicalStationSignedBlock.scale
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (inv_ne_zero b.ne'))) (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr a.ne'))
  exact inv_mul_cancel_right₀ price _

include shared near lead obeys in
theorem bounded:
    ∃C:ℝ,0≤C ∧ ∀ᶠi in u,∀v:(Bel R.family.book).Field d,
      ∑e,‖coefficient F J Z d (books (age i)) v e‖≤C*cost R.family v:=by
  let b:=Module.finBasis ℂ ((Bel R.family.book).Field d)
  let V:=fun y:(Bel R.family.book).Field d=>(R.family.labels.level d).coeffSize (ladder R.family d y)
  have cv:Continuous V:=by
    change Continuous (fun y=>∑e,‖(ladder R.family d y) e‖)
    fun_prop
  let M:=∑j,(V (b j)+1)
  have pos (y):0≤V y:=Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  have mp:0≤M:=Finset.sum_nonneg (fun j _=>by have:=pos (b j);linarith)
  refine ⟨M,mp,?_⟩
  have cap (j):V (b j)+1≤M:=Finset.single_le_sum (f:=fun k=>V (b k)+1)
    (fun k _=>by have:=pos (b k);linarith) (Finset.mem_univ j)
  have basis:∀ᶠi in u,∀j,V (input F J Z d (books (age i)) (b j))≤M:=by
    apply Filter.eventually_all.mpr
    intro j
    have h:=WilsonPhysicalWeakHomogeneousHome.direction F J simple a books shared Z lead obeys u age near d (b j)
    exact ((cv.continuousAt.tendsto.comp h).eventually (eventually_lt_nhds (lt_add_one (V (b j))))).mono
      (fun _ s=>s.le.trans (cap j))
  filter_upwards [basis] with i funded v
  let B:=books (age i)
  let H:=((B.V d).symm.toLinearMap.comp (WilsonPositionHomogeneousFrame.homogeneous F J Z (age i).val d).toLinearMap)
  let L:=(ladder R.family d).toLinearMap.comp H
  have exactName:L v=∑j,(b.repr v) j • L (b j):=by
    nth_rw 1 [←b.sum_repr v];simp only [map_sum,map_smul]
  change (R.family.labels.level d).coeffSize (L v)≤_
  rw [exactName]
  calc
    _=∑k,‖∑j,(b.repr v) j * L (b j) k‖:=by simp [Labels.Frame.coeffSize]
    _≤∑k,∑j,‖(b.repr v) j * L (b j) k‖:=Finset.sum_le_sum fun _ _=>norm_sum_le _ _
    _=∑j,‖(b.repr v) j‖*(R.family.labels.level d).coeffSize (L (b j)):=by
      rw [Finset.sum_comm];simp [Labels.Frame.coeffSize,Finset.mul_sum]
    _≤∑j,‖(b.repr v) j‖*M:=Finset.sum_le_sum fun j _=>mul_le_mul_of_nonneg_left (funded j) (norm_nonneg _)
    _=_:=by rw [←Finset.sum_mul,mul_comm];rfl

end YM.Integration.WilsonPhysicalActualWeakNames
