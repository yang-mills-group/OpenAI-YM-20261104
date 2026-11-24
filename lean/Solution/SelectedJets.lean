import YM.PhysMS.Frame.Stage
import YM.PhysMS.Frame.Phases
import YM.Integration.ManuscriptTraceTests
import YM.Pert.FirstTarget

/-! Marked Maxwell jets in each phase of the same Wilson refinement.
The phase estimate is made in a leading field frame on the selected continuum.
The marked stress is recovered from its separated free-field tests in grade four. -/

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

noncomputable section
namespace YM.Existence.SelectedJets.SparseFrame
open Function Filter Set Climb Trace.Pilot
open scoped Topology BigOperators Classical

variable {G:Gauge}{C:Family G}{S:Table C.book}

def splice (X:Scaling S)(J:ℝ→PhysMS.tower S)(s:ℝ):PhysMS.tower S:=
  if h:∃k,X.r k=s then X.U h.choose else J s

theorem selected (X:Scaling S)(J:ℝ→PhysMS.tower S)(k:ℕ):
    splice X J (X.r k)=X.U k:=by
  have hit:∃i,X.r i=X.r k:=⟨k,rfl⟩
  rw [splice,dif_pos hit,X.later.injective hit.choose_spec]

theorem away (X:Scaling S)(J:ℝ→PhysMS.tower S)(s:ℝ)(miss:¬∃k,X.r k=s):
    splice X J s=J s:=dif_neg miss

theorem original (X:Scaling S)(J:ℝ→PhysMS.tower S)(P:ℝ→PhysMS.tower S→Prop)
    (all:∀ᶠ s:ℝ in trail,P s (J s))(onX:∀ᶠ k:ℕ in atTop,P (X.r k) (X.U k)):
    (∀k:ℕ,splice X J (X.r k)=X.U k) ∧ ∀ᶠ s:ℝ in trail,P s (splice X J s):=by
  obtain ⟨k,hk⟩:=eventually_atTop.1 onX
  have before:∀ᶠ s:ℝ in trail,s<X.r k:=
    (eventually_lt_nhds (X.positive k)).filter_mono nhdsWithin_le_nhds
  refine ⟨selected X J,?_⟩
  filter_upwards [all,before] with s paid smaller
  by_cases hit:∃i,X.r i=s
  · obtain ⟨i,rfl⟩:=hit
    rw [selected]
    apply hk i
    by_contra bad
    exact lt_asymm smaller (X.later (lt_of_not_ge bad))
  · rw [away X J s hit]
    exact paid

theorem convergence {Y:Type*}[TopologicalSpace Y](X:Scaling S)(J:ℝ→PhysMS.tower S)
    (app:ℝ→PhysMS.tower S→Y)(y:Y)(all:Tendsto (fun s:ℝ=>app s (J s)) trail (𝓝 y))
    (onX:Tendsto (fun k:ℕ=>app (X.r k) (X.U k)) atTop (𝓝 y)):
    Tendsto (fun s:ℝ=>app s (splice X J s)) trail (𝓝 y):=by
  intro B near
  exact (original X J (fun s U=>app s U∈B) (all near) (onX near)).2

theorem sparse (X:Scaling S):Tendsto X.r atTop trail:=
  tendsto_nhdsWithin_iff.mpr ⟨X.drips,Eventually.of_forall X.positive⟩

end YM.Existence.SelectedJets.SparseFrame
end

noncomputable section
namespace YM.Existence.SelectedJets.SparseLeading
open Function Filter Set MeasureTheory Spec Extraction Table Maxwell Maxwell.Free
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato Table
open PhysMS.Frame
open scoped Topology BigOperators Classical

variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
theorem unmarked (F:Final C f S)(X:Scaling S)(first:Pert.FirstExtension F X)
    {n:ℕ}(d:Caps n)(v:MaxwellSlots C d)(j:ℕ){K:Set (Points n)}
    (compact:IsCompact K)(inside:K⊆conf n):
    TendstoUniformlyOn (fun k:ℕ=>iteratedFDeriv ℝ j (measured F none (X.U k) v (X.r k)))
      (iteratedFDeriv ℝ j (WickGoal v)) atTop K:=by
  let q:Pert.Slots n→(Maxwell.freeTable C.labels).Tag:=fun i=>⟨d i,v i⟩
  let ab:Pert.Slots n→Axis×Axis:=fun _=>(0,0)
  have physical (k:ℕ): (fun z=>Ward.disc (Pert.scaledPhysical X F.sector.energy k q (fun _=>false) ab) (X.r k • z))=
      measured F none (X.U k) v (X.r k):=by
    rfl
  have free: Ward.disc (Pert.freeWithStress C.labels q (fun _=>false) ab)=WickGoal v:=by
    rfl
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε pos
  have bound:=first.jets n j q (fun _=>false) ab compact inside (half_pos pos)
  filter_upwards [bound] with k paid x hx
  have close:=paid x hx
  rw [physical,free] at close
  rw [dist_comm,dist_eq_norm]
  exact lt_of_le_of_lt close (half_lt_self pos)

theorem original (F:Final C f S)(X:Scaling S)(first:Pert.FirstExtension F X)(J:ℝ→PhysMS.tower S)
    (grant:Leading F J):
    (∀k:ℕ,SparseFrame.splice X J (X.r k)=X.U k) ∧ Leading F (SparseFrame.splice X J):=by
  refine ⟨SparseFrame.selected X J,?_⟩
  constructor
  · intro d
    exact (SparseFrame.original X J (fun _ U=>Spin.realH F.room.kernel.spin (Maxwell.Free.spin_free C.labels) (U d)) (grant.equivariant d) (first.fit.hsym d)).2
  · intro d e h
    exact (SparseFrame.original X J (fun _ U=>∀v,U e ((Maxwell.Free.scheme C.labels).rise h v)=F.sector.derivatives.rise h (U d v)) (grant.raised h) (first.fit.rises d e h)).2
  · intro d
    exact (SparseFrame.original X J (fun _ U=>U d ((Bel C.book).unit d)=S.unit d) (grant.unit d) (first.fit.units d)).2
  · intro n d v j K compact inside
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε pos
    have whole:=Metric.tendstoUniformlyOn_iff.mp (grant.lead n d v j K compact inside) ε pos
    have observed:=Metric.tendstoUniformlyOn_iff.mp (unmarked F X first d v j compact inside) ε pos
    exact (SparseFrame.original X J (fun s U=>∀x∈K,dist (iteratedFDeriv ℝ j (WickGoal v) x)
      (iteratedFDeriv ℝ j (measured F none U v s) x)<ε) whole observed).2

end YM.Existence.SelectedJets.SparseLeading
end

noncomputable section
namespace YM.Existence.SelectedJets.StressRows
open Function Filter Set MeasureTheory Spec Extraction Table Maxwell Maxwell.Free
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato Table
open PhysMS.Frame
open scoped Topology BigOperators Classical

open scoped Matrix

variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}
structure Survey (C:Family G) where
  guests:ℕ
  earlier:Fin guests→(Bel C.book).Tag
  spot:Points (guests+1)
  separate:spot∈conf (guests+1)

def dims (P:Survey C):Caps (P.guests+1):=Fin.cons 4 (fun i=>(P.earlier i).1)
def fixed (P:Survey C):(i:Fin (P.guests+1))→(Bel C.book).Field (dims P i):=
  Fin.cons 0 (fun i=>(P.earlier i).2)
def seats (P:Survey C)(u:(Bel C.book).Field 4):(i:Fin (P.guests+1))→(Bel C.book).Field (dims P i):=
  Function.update (fixed P) 0 u
def tickets (P:Survey C)(u:(Bel C.book).Field 4):Fin (P.guests+1)→(Bel C.book).Tag:=
  fun i=>⟨dims P i,seats P u i⟩

def free (P:Survey C):(Bel C.book).Field 4→ₗ[ℂ]ℂ:=
  ((Bel C.book).classMoment (Bel C.book) (dims P) P.spot).toLinearMap (fixed P) 0

def raw (P:Survey C)(X:Scaling S)(k:ℕ):S.Field 4→ₗ[ℂ]ℂ:=
  (S.classMoment S (dims P) (X.r k • P.spot)).toLinearMap (fun i=>X.U k (dims P i) (fixed P i)) 0

def mean (P:Survey C)(X:Scaling S)(k:ℕ):(Bel C.book).Field 4→ₗ[ℂ]ℂ:=
  (raw P X k).comp (X.U k 4).toLinearMap

def physical (F:Final C f S)(X:Scaling S)(k:ℕ)(a b:Axis):S.Field 4:=
  ((X.r k^4:ℝ):ℂ) • F.sector.energy a b

def born (F:Final C f S)(X:Scaling S)(k:ℕ)(a b:Axis):(Bel C.book).Field 4:=
  (X.U k 4).symm (physical F X k a b)

theorem reader (F:Final C f S)(X:Scaling S)(P:Survey C)(u:(Bel C.book).Field 4)(k:ℕ):
    measured F none (X.U k) (seats P u) (X.r k) P.spot=mean P X k u:=by
  change (S.classMoment S (dims P) (X.r k • P.spot)) (fun i=>X.U k (dims P i) (seats P u i))=
    (S.classMoment S (dims P) (X.r k • P.spot)) (Function.update (fun i=>X.U k (dims P i) (fixed P i)) 0 (X.U k 4 u))
  congr 1
  funext i
  by_cases primary:i=0
  · subst i
    simp [seats,dims]
    rfl
  · simp [seats,Function.update_of_ne primary]

theorem freeRead (P:Survey C)(u:(Bel C.book).Field 4):WickGoal (seats P u) P.spot=free P u:=rfl

theorem observed (F:Final C f S)(X:Scaling S)(P:Survey C)(k:ℕ)(a b:Axis):
    Ward.disc (Pert.scaledPhysical X F.sector.energy k (tickets P 0) (fun i=>decide (i=0)) (fun _=>(a,b)))
      (X.r k • P.spot)=raw P X k (physical F X k a b):=by
  have issued: Pert.scaledPhysical X F.sector.energy k (tickets P 0) (fun i=>decide (i=0)) (fun _=>(a,b))=
      (fun i=>⟨dims P i,(Function.update (fun i=>X.U k (dims P i) (fixed P i)) 0 (physical F X k a b)) i⟩):=by
    funext i
    by_cases home:i=0
    · subst i
      simp [Pert.scaledPhysical,physical,dims]
      rfl
    · simp [Pert.scaledPhysical,tickets,seats,home]
      rfl
  rw [issued]
  rfl

theorem underlying (P:Survey C)(a b:Axis):
    Ward.disc (Pert.freeWithStress C.labels (tickets P 0) (fun i=>decide (i=0)) (fun _=>(a,b))) P.spot=
      free P (Pert.freeStress C.labels a b):=by
  have issued:Pert.freeWithStress C.labels (tickets P 0) (fun i=>decide (i=0)) (fun _=>(a,b))=
      tickets P (Pert.freeStress C.labels a b):=by
    funext i
    by_cases home:i=0
    · subst i
      simp [Pert.freeWithStress,tickets,seats,dims]
      rfl
    · simp [Pert.freeWithStress,tickets,seats,home]
  rw [issued]
  rfl

theorem original {I:Type*}[Fintype I][DecidableEq I](B:Module.Basis I ℂ ((Bel C.book).Field 4))(rows:I→Survey C)
    (F:Final C f S)(X:Scaling S)(k:ℕ)(a b:Axis):
    (fun i j=>mean (rows i) X k (B j)) *ᵥ (fun j=>B.repr (born F X k a b) j)=
      (fun i=>raw (rows i) X k (physical F X k a b)):=by
  funext i
  have paid:=congrArg (mean (rows i) X k) (B.sum_repr (born F X k a b))
  simp only [map_sum,map_smul,smul_eq_mul] at paid
  change (∑j,mean (rows i) X k (B j)*B.repr (born F X k a b) j)=_
  calc
    _ = ∑j,B.repr (born F X k a b) j*mean (rows i) X k (B j):=by apply Finset.sum_congr rfl;intro j _;ring
    _ = mean (rows i) X k (born F X k a b):=paid
    _ = _:=by simp [mean,born]

end YM.Existence.SelectedJets.StressRows
end

noncomputable section
namespace YM.Existence.SelectedJets.StressDetector
open Function Filter Set MeasureTheory Spec Extraction Table Maxwell Maxwell.Free
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato Table
open PhysMS.Frame
open scoped Topology BigOperators Classical

open scoped Matrix

open StressRows
variable {G:Gauge}{C:Family G}
def survey (C:Family G)(w:Maxwell.ProbeFamily G):Survey C:=
  ⟨w.n,fun i=>⟨w.d i,(Maxwell.Free.fields C.labels _).symm (w.exterior i)⟩,w.x,w.clear⟩

theorem placed (w:Maxwell.ProbeFamily G)(u:(Bel C.book).Field 4):
    free (survey C w) u=w.test 4 (Maxwell.Free.fields C.labels 4 u):=by
  rw [Maxwell.test_formula]
  change ((Bel C.book).useAt (Bel C.book) w.x (tickets (survey C w) u))=_
  rw [Maxwell.Free.display]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp [Function.comp_apply,Maxwell.Free.supply,Maxwell.Free.address,tickets,seats,dims,survey]
    rfl
  · simp [Function.comp_apply,Maxwell.Free.supply,Maxwell.Free.address,tickets,seats,fixed,dims,survey]
    change (Maxwell.Free.fields C.labels (w.d j) ((Maxwell.Free.fields C.labels (w.d j)).symm (w.exterior j))).val=(w.exterior j).val
    rw [LinearEquiv.apply_symm_apply]

theorem separates (u:(Bel C.book).Field 4)(all:∀P:Survey C,free P u=0):u=0:=by
  have empty:Maxwell.Free.fields C.labels 4 u∈Maxwell.residual G 4:=by
    rw [Maxwell.residual,LinearMap.mem_ker]
    funext w
    exact (placed (C:=C) w u).symm.trans (all (survey C w))
  rw [Maxwell.Free.no_residual,Submodule.mem_bot] at empty
  exact (Maxwell.Free.fields C.labels 4).injective (empty.trans (map_zero _).symm)

theorem original : Submodule.span ℂ (Set.range (free (C:=C)))=⊤:=by
  let D:=Submodule.span ℂ (Set.range (free (C:=C)))
  have zero:D.dualCoannihilator=⊥:=by
    apply le_antisymm _ bot_le
    intro x h
    change x=0
    apply separates
    intro P
    exact (Submodule.mem_dualCoannihilator x).mp h _ (Submodule.subset_span ⟨P,rfl⟩)
  change D=⊤
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W:=D),zero,Submodule.dualAnnihilator_bot]

end YM.Existence.SelectedJets.StressDetector
end

noncomputable section
namespace YM.Existence.SelectedJets.MeasuredMarks
open Function Filter Set MeasureTheory Spec Extraction Table Maxwell Maxwell.Free
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato Table
open PhysMS.Frame
open scoped Topology BigOperators Classical

variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}
theorem orderZero {n:ℕ}(x:Points n)(F G:Points n→ℂ):
    ‖iteratedFDeriv ℝ 0 F x-iteratedFDeriv ℝ 0 G x‖=‖F x-G x‖:=by
  calc
    _=‖iteratedFDeriv ℝ 0 (fun y=>F y-G y) x‖:=by
      congr 1
    _=‖F x-G x‖:=norm_iteratedFDeriv_zero

theorem original (F:Final C f S)(X:Scaling S)(first:Pert.FirstExtension F X){n:ℕ}
    (q:Fin n→(Bel C.book).Tag)(mask:Fin n→Bool)(ab:Fin n→Axis×Axis)(x:Points n)(separated:x∈conf n):
    Tendsto (fun k:ℕ=>Ward.disc (Pert.scaledPhysical X F.sector.energy k q mask ab) (X.r k • x)) atTop
      (𝓝 (Ward.disc (Pert.freeWithStress C.labels q mask ab) x)):=by
  apply Metric.tendsto_nhds.mpr
  intro ε pos
  have bill:=first.jets n 0 q mask ab isCompact_singleton (Set.singleton_subset_iff.mpr separated) (half_pos pos)
  filter_upwards [bill] with k right
  have cost:=right x (Set.mem_singleton x)
  rw [orderZero] at cost
  rw [dist_eq_norm]
  exact lt_of_le_of_lt cost (half_lt_self pos)

theorem unmarked (F:Final C f S)(X:Scaling S)(first:Pert.FirstExtension F X){n:ℕ}
    (d:Caps n)(v:MaxwellSlots C d)(x:Points n)(sep:x∈conf n):
    Tendsto (fun k:ℕ=>measured F none (X.U k) v (X.r k) x) atTop (𝓝 (WickGoal v x)):=by
  exact original F X first (fun i=>⟨d i,v i⟩) (fun _=>false) (fun _=>(0,0)) x sep

end YM.Existence.SelectedJets.MeasuredMarks
end

noncomputable section
namespace YM.Existence.SelectedJets.GramAccount
open Filter Function Matrix
open scoped Topology BigOperators Matrix Classical

variable {I:Type*}[Fintype I][DecidableEq I]
theorem recover (M:Matrix I I ℂ)(paid:IsUnit M.det)(v:I→ℂ):
    M⁻¹ *ᵥ (M *ᵥ v)=v:=by
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ paid,Matrix.one_mulVec]

theorem original (A:Matrix I I ℂ)(c:I→ℂ)(Ak:ℕ→Matrix I I ℂ)(b E:ℕ→I→ℂ)
    (dual:IsUnit A.det)(gram:Tendsto Ak atTop (𝓝 A))
    (marked:Tendsto b atTop (𝓝 (A *ᵥ c)))(read:∀ᶠ k in atTop,Ak k *ᵥ E k=b k):
    Tendsto E atTop (𝓝 c) ∧ ∃C:ℝ,0<C ∧ ∀ᶠ k in atTop,(∑i,‖E k i‖)≤C:=by
  have nonzero:A.det≠0:=isUnit_iff_ne_zero.mp dual
  have dets:=((continuous_id.matrix_det).continuousAt (x:=A)).tendsto.comp gram
  have mature:=dets.eventually_ne nonzero
  have inverse:ContinuousAt Inv.inv A:=
    continuousAt_matrix_inv A (by rw [Ring.inverse_eq_inv'];exact continuousAt_inv₀ nonzero)
  have inverses:Tendsto (fun k=>(Ak k)⁻¹) atTop (𝓝 A⁻¹):=inverse.tendsto.comp gram
  have rhs:Tendsto (fun k=>(Ak k)⁻¹ *ᵥ b k) atTop (𝓝 (A⁻¹ *ᵥ (A *ᵥ c))):=by
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_finsetSum _ (fun j _=>((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp inverses i) j).mul
      (tendsto_pi_nhds.mp marked j)))
  rw [recover A dual c] at rhs
  have limit:Tendsto E atTop (𝓝 c):=by
    apply rhs.congr'
    filter_upwards [mature,read] with k allowed bill
    rw [← bill,recover (Ak k) (isUnit_iff_ne_zero.mpr allowed)]
  have salaries:Tendsto (fun k=>∑i,‖E k i‖) atTop (𝓝 (∑i,‖c i‖)):=
    tendsto_finsetSum _ (fun i _=>(tendsto_pi_nhds.mp limit i).norm)
  refine ⟨limit,(∑i,‖c i‖)+1,by positivity,?_⟩
  exact (salaries.eventually (gt_mem_nhds (lt_add_one _))).mono fun k h=>le_of_lt h

end YM.Existence.SelectedJets.GramAccount
end

noncomputable section
namespace YM.Existence.SelectedJets.MeasuredStress
open Function Filter Set MeasureTheory Spec Extraction Table Maxwell Maxwell.Free
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato Table
open PhysMS.Frame
open scoped Topology BigOperators Classical

open scoped Matrix

open StressRows
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}
theorem reference {I:Type*}[Fintype I][DecidableEq I](B:Module.Basis I ℂ ((Bel C.book).Field 4))
    (P:I→Survey C)(v:(Bel C.book).Field 4):
    (fun i j=>free (P i) (B j)) *ᵥ (fun j=>B.repr v j)=(fun i=>free (P i) v):=by
  funext i
  have word:=congrArg (free (P i)) (B.sum_repr v)
  simp only [map_sum,map_smul,smul_eq_mul] at word
  change (∑j,free (P i) (B j)*B.repr v j)=_
  calc
    _=∑j,B.repr v j*free (P i) (B j):=by apply Finset.sum_congr rfl;intro j _;ring
    _=free (P i) v:=word

theorem original {I:Type*}[Fintype I][DecidableEq I](B:Module.Basis I ℂ ((Bel C.book).Field 4))
    (P:I→Survey C)(dual:IsUnit (Matrix.det (fun i j=>free (P i) (B j))))
    (F:Final C f S)(X:Scaling S)(first:Pert.FirstExtension F X)(a b:Axis):
    Tendsto (fun k:ℕ=>fun j=>B.repr (born F X k a b) j) atTop
      (𝓝 (fun j=>B.repr (Pert.freeStress C.labels a b) j)) ∧
    ∃V:ℝ,0<V ∧ ∀ᶠ k in atTop,(∑j,‖B.repr (born F X k a b) j‖)≤V:=by
  let A:Matrix I I ℂ:=fun i j=>free (P i) (B j)
  let Ak:ℕ→Matrix I I ℂ:=fun k i j=>mean (P i) X k (B j)
  let y:ℕ→I→ℂ:=fun k i=>raw (P i) X k (physical F X k a b)
  let c:I→ℂ:=fun j=>B.repr (Pert.freeStress C.labels a b) j
  have gram:Tendsto Ak atTop (𝓝 A):=by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have paid:=MeasuredMarks.unmarked F X first (dims (P i)) (seats (P i) (B j)) (P i).spot (P i).separate
    simpa only [reader,freeRead] using paid
  have stress:Tendsto y atTop (𝓝 (A *ᵥ c)):=by
    change Tendsto y atTop (𝓝 ((fun i j=>free (P i) (B j)) *ᵥ (fun j=>B.repr (Pert.freeStress C.labels a b) j)))
    rw [reference]
    apply tendsto_pi_nhds.mpr
    intro i
    have paid:=MeasuredMarks.original F X first (tickets (P i) 0) (fun i=>decide (i=0)) (fun _=>(a,b)) (P i).spot (P i).separate
    simpa only [StressRows.observed,StressRows.underlying] using paid
  exact GramAccount.original A c Ak y (fun k j=>B.repr (born F X k a b) j) dual gram stress
    (Eventually.of_forall fun k=>StressRows.original B P F X k a b)

end YM.Existence.SelectedJets.MeasuredStress
end

noncomputable section
namespace YM.Existence.SelectedJets.StressCapital
open Function Filter Set MeasureTheory Spec Extraction Table Maxwell Maxwell.Free
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato Table
open PhysMS.Frame
open scoped Topology BigOperators Classical

open scoped Matrix

open StressRows

variable {G:Gauge}{C:Family G}

theorem booked (C:Family G):∃(n:ℕ)(B:Module.Basis (Fin n) ℂ ((Bel C.book).Field 4))(P:Fin n→Survey C),
    (fun i j=>free (P i) (B j))=(1:Matrix (Fin n) (Fin n) ℂ):=by
  let V:=(Bel C.book).Field 4
  obtain ⟨D,inside,covered,indep⟩:=exists_linearIndependent ℂ (Set.range (free (C:=C)))
  have total:⊤≤Submodule.span ℂ (Set.range ((↑):D→Module.Dual ℂ V)):=by
    rw [Subtype.range_coe,covered,StressDetector.original]
  let f:Module.Basis D ℂ (Module.Dual ℂ V):=Module.Basis.mk indep total
  letI:Fintype D:=FiniteDimensional.fintypeBasisIndex f
  let e:=Fintype.equivFin D
  let f':=f.reindex e
  let B:=f'.dualBasis.map (Module.evalEquiv ℂ V).symm
  have named (i:Fin (Fintype.card D)):∃P:Survey C,free P=f' i:=by
    have row:=inside (e.symm i).property
    simpa only [f',Module.Basis.reindex_apply,f,Module.Basis.mk_apply,Set.mem_range] using row
  choose P matchP using named
  refine ⟨_,B,P,?_⟩
  ext i j
  rw [matchP]
  change f' i ((Module.evalEquiv ℂ V).symm (f'.dualBasis j))=_
  rw [Module.apply_evalEquiv_symm_apply,Module.Basis.dualBasis_apply_self]
  simp [Matrix.one_apply]

theorem original (C:Family G):∃(n:ℕ)(B:Module.Basis (Fin n) ℂ ((Bel C.book).Field 4))(P:Fin n→Survey C),
    (fun i j=>free (P i) (B j))=(1:Matrix (Fin n) (Fin n) ℂ) ∧
    ∀{S:Table C.book}{f:Extraction.Order}(F:Final C f S)(X:Scaling S),Pert.FirstExtension F X→∀a b:Axis,
      Tendsto (fun k:ℕ=>fun j=>B.repr (born F X k a b) j) atTop
        (𝓝 (fun j=>B.repr (Pert.freeStress C.labels a b) j)) ∧
      ∃V:ℝ,0<V ∧ ∀ᶠ k in atTop,(∑j,‖B.repr (born F X k a b) j‖)≤V:=by
  obtain ⟨n,B,P,dual⟩:=booked C
  refine ⟨n,B,P,dual,?_⟩
  intro S f F X first a b
  exact MeasuredStress.original B P (by rw [dual];simp) F X first a b

end YM.Existence.SelectedJets.StressCapital
end

noncomputable section
namespace YM.Existence.SelectedJets.JetSalary
open Finset Function Filter
open scoped BigOperators Classical
variable {n:ℕ}{V:Fin n→Type*}{I:Fin n→Type*}{W:Type*}
variable [∀i,AddCommGroup (V i)][∀i,Module ℂ (V i)][∀i,Fintype (I i)]
variable [NormedAddCommGroup W][NormedSpace ℂ W]
def salary (B:∀i,Module.Basis (I i) ℂ (V i))(v:(i:Fin n)→V i):ℝ:=
  ∏i,∑j,‖(B i).repr (v i) j‖
theorem original (D:MultilinearMap ℂ V W)(B:∀i,Module.Basis (I i) ℂ (V i))
    (v:(i:Fin n)→V i)(a:ℝ)(paid:∀j:(i:Fin n)→I i,‖D (fun i=>B i (j i))‖≤a):
    ‖D v‖≤a*salary B v:=by
  have rep: D v=∑j:((i:Fin n)→I i),(∏i,(B i).repr (v i) (j i)) • D (fun i=>B i (j i)):=by
    calc
      _=D (fun i=>∑j,(B i).repr (v i) j • B i j):=by congr 1;funext i;exact ((B i).sum_repr (v i)).symm
      _=∑j:((i:Fin n)→I i),D (fun i=>(B i).repr (v i) (j i) • B i (j i)):=D.map_sum _
      _=_:=by simp only [D.map_smul_univ]
  rw [rep]
  calc
    _≤∑j:((i:Fin n)→I i),‖(∏i,(B i).repr (v i) (j i)) • D (fun i=>B i (j i))‖:=norm_sum_le _ _
    _≤∑j:((i:Fin n)→I i),(∏i,‖(B i).repr (v i) (j i)‖)*a:=by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul,norm_prod]
      exact mul_le_mul_of_nonneg_left (paid j) (Finset.prod_nonneg fun _ _=>norm_nonneg _)
    _=a*salary B v:=by
      rw [← Finset.sum_mul,mul_comm]
      congr 1
      unfold salary
      rw [Finset.prod_univ_sum]
      simp
end YM.Existence.SelectedJets.JetSalary
end

noncomputable section
namespace YM.Existence.SelectedJets.StressMenus
open Function Filter Set MeasureTheory Spec Extraction Table Maxwell Maxwell.Free
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato Table
open PhysMS.Frame
open scoped Topology BigOperators Classical

open scoped Matrix

open StressRows

variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
def height (t:(Bel C.book).Tag):Bool→ℕ
  | true=>4
  | false=>t.1
def width {D:ℕ}(t:(Bel C.book).Tag):Bool→ℕ
  | true=>D
  | false=>Module.finrank ℂ ((Bel C.book).Field t.1)
def basis {D:ℕ}(B:Module.Basis (Fin D) ℂ ((Bel C.book).Field 4))(t:(Bel C.book).Tag):
    ∀flag,Module.Basis (Fin (width (D:=D) t flag)) ℂ ((Bel C.book).Field (height t flag))
  | true=>B
  | false=>Module.finBasis ℂ ((Bel C.book).Field t.1)
def pupil (F:Final C f S)(X:Scaling S)(t:(Bel C.book).Tag)(ab:Axis×Axis)(k:ℕ):
    ∀flag,(Bel C.book).Field (height t flag)
  | true=>born F X k ab.1 ab.2
  | false=>t.2

theorem original (C:Family G):∃(D:ℕ)(B:Module.Basis (Fin D) ℂ ((Bel C.book).Field 4)),
    ∀{S:Table C.book}{f:Extraction.Order}(F:Final C f S)(X:Scaling S),Pert.FirstExtension F X→
      ∀{n:ℕ}(q:Fin n→(Bel C.book).Tag)(marks:Fin n→Bool)(ab:Fin n→Axis×Axis),∃V:ℝ,0<V ∧
        ∀ᶠ k in atTop,JetSalary.salary (fun i=>basis B (q i) (marks i))
          (fun i=>pupil F X (q i) (ab i) k (marks i))≤V:=by
  obtain ⟨D,B,P,_,budget⟩:=StressCapital.original C
  refine ⟨D,B,?_⟩
  intro S f F X earned n q marks ab
  have own (t:(Bel C.book).Tag)(a:Axis×Axis)(flag:Bool):∃v:ℝ,0<v ∧∀ᶠk:ℕ in atTop,
      (∑j,‖(basis B t flag).repr (pupil F X t a k flag) j‖)≤v:=by
    cases flag with
    | true=>exact (budget F X earned a.1 a.2).2
    | false=>
      let s:=∑j,‖(basis B t false).repr t.2 j‖
      have hn : 0 ≤ s :=Finset.sum_nonneg fun _ _=>norm_nonneg _
      refine ⟨s+1,by positivity,Filter.Eventually.of_forall fun _=>?_⟩
      change s ≤ s+1
      linarith
  choose v positive paid using fun i=>own (q i) (ab i) (marks i)
  refine ⟨∏i,v i,Finset.prod_pos fun i _=>positive i,?_⟩
  filter_upwards [Filter.eventually_all.mpr paid] with k budget
  exact Finset.prod_le_prod (fun i _=>Finset.sum_nonneg fun _ _=>norm_nonneg _) fun i _=>budget i

end YM.Existence.SelectedJets.StressMenus
end

noncomputable section
namespace YM.Existence.SelectedJets.StressEntry
open Function Filter Set MeasureTheory Spec Extraction Table Maxwell Maxwell.Free
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato Table
open PhysMS.Frame
open scoped Topology BigOperators Classical

open scoped Matrix

open StressRows

variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}

open StressMenus
theorem filed (F:Final C f S)(X:Scaling S)(k:ℕ){n:ℕ}
    (q:Fin n→(Bel C.book).Tag)(marks:Fin n→Bool)(ab:Fin n→Axis×Axis):
    Pert.scaledPhysical X F.sector.energy k q marks ab =
      fun i=>⟨height (q i) (marks i),X.U k (height (q i) (marks i)) (pupil F X (q i) (ab i) k (marks i))⟩:=by
  funext i
  cases key:marks i
  · simp [Pert.scaledPhysical,key,height,pupil]
    rfl
  · simp [Pert.scaledPhysical,key,height,pupil]
    unfold StressRows.born
    calc
      _=StressRows.physical F X k (ab i).1 (ab i).2:=by simp [StressRows.physical]
      _=_:=((X.U k 4).apply_symm_apply (StressRows.physical F X k (ab i).1 (ab i).2)).symm

theorem original (F:Final C f S)(X:Scaling S)(k:ℕ){n:ℕ}
    (q:Fin n→(Bel C.book).Tag)(marks:Fin n→Bool)(ab:Fin n→Axis×Axis)(p:Viewers F):
    measured F p (X.U k) (fun i=>pupil F X (q i) (ab i) k (marks i)) (X.r k)=
      fun x=>S.useAt (spectator F p) (X.r k • x) (Pert.scaledPhysical X F.sector.energy k q marks ab):=by
  rw [filed F X]
  rfl

end YM.Existence.SelectedJets.StressEntry
end

noncomputable section
namespace YM.Existence.SelectedJets.SparsePhases
open Function Filter Set MeasureTheory Spec Extraction Table Maxwell Maxwell.Free
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato Table
open PhysMS.Frame
open scoped Topology BigOperators Classical

variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
theorem original (F:Final C f S)(X:Scaling S)(first:Pert.FirstExtension F X)
    (J:ℝ→PhysMS.tower S)(leading:Leading F J)(simple:G.Simple)
    (Q:OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(foundation:OPE.Orbits.Foundation F Q)
    {n:ℕ}(d:Caps n)(v:MaxwellSlots C d)(j:ℕ){K:Set (Points n)}(compact:IsCompact K)(inside:K⊆conf n):
    (∀k:ℕ,SparseFrame.splice X J (X.r k)=X.U k) ∧
    ∀ᶠ k:ℕ in atTop,∀x∈K,∀p q:Viewers F,
      ‖iteratedFDeriv ℝ j (measured F p (X.U k) v (X.r k)) x-
        iteratedFDeriv ℝ j (measured F q (X.U k) v (X.r k)) x‖≤(X.r k)^3:=by
  obtain ⟨fixed,price⟩:=SparseLeading.original F X first J leading
  obtain ⟨M,hM,η,hη,room⟩:=compact_within K compact inside
  have fee:=PhysMS.Frame.within_price F Q (SparseFrame.splice X J) price simple X foundation M η 1 j v zero_lt_one hM hη
  refine ⟨fixed,?_⟩
  filter_upwards [(SparseFrame.sparse X).eventually fee] with k enclosed x hx p q
  have earned:=enclosed x (room x hx) p q
  rw [fixed k] at earned
  simpa only [show (4:ℝ)-1=(3:ℕ) by norm_num,Real.rpow_natCast] using earned

end YM.Existence.SelectedJets.SparsePhases
end

noncomputable section
namespace YM.Existence.SelectedJets.MovingJets
open Function Filter Set MeasureTheory Spec Extraction Table Maxwell Maxwell.Free
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato Table
open PhysMS.Frame
open scoped Topology BigOperators Classical

variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}

theorem balance {n:ℕ}(F:Final C f S)(X:Scaling S)(d:Caps n)(j:ℕ)(k:ℕ)(x:Points n)(hx:x∈conf n)
    (p q:Viewers F){I:Fin n→Type*}[∀i,Fintype (I i)]
    (B:∀i,Module.Basis (I i) ℂ ((Spin.comparator C.book).Field (d i)))
    (v:MaxwellSlots C d)(a:ℝ)
    (paid:∀t:(i:Fin n)→I i,
      ‖iteratedFDeriv ℝ j (measured F p (X.U k) (fun i=>B i (t i)) (X.r k)) x-
        iteratedFDeriv ℝ j (measured F q (X.U k) (fun i=>B i (t i)) (X.r k)) x‖≤a):
    ‖iteratedFDeriv ℝ j (measured F p (X.U k) v (X.r k)) x-
      iteratedFDeriv ℝ j (measured F q (X.U k) v (X.r k)) x‖≤a*JetSalary.salary B v:=by
  let wallet:=fun i=>(X.U k (d i)).toLinearMap
  let D:=((jet F j p d (X.r k) x)-(jet F j q d (X.r k) x)).compLinearMap wallet
  have seen (v:MaxwellSlots C d):D v=iteratedFDeriv ℝ j (measured F p (X.U k) v (X.r k)) x-
      iteratedFDeriv ℝ j (measured F q (X.U k) v (X.r k)) x:=by
    change jet F j p d (X.r k) x (fun i=>X.U k (d i) (v i))-
      jet F j q d (X.r k) x (fun i=>X.U k (d i) (v i))=_
    rw [jet_from_measure F _ _ _ _ j (Work.A05.smul_conf (X.positive k) hx),
      jet_from_measure F _ _ _ _ j (Work.A05.smul_conf (X.positive k) hx)]
  rw [←seen v]
  exact JetSalary.original D B v a fun t=>by rw [seen];exact paid t

theorem original (F:Final C f S)(X:Scaling S)(first:Pert.FirstExtension F X)
    (J:ℝ→PhysMS.tower S)(leading:Leading F J)(simple:G.Simple)
    (Q:OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(foundation:OPE.Orbits.Foundation F Q)
    {n:ℕ}(d:Caps n){I:Fin n→Type*}[∀i,Fintype (I i)]
    (B:∀i,Module.Basis (I i) ℂ ((Spin.comparator C.book).Field (d i)))
    (j:ℕ){K:Set (Points n)}(compact:IsCompact K)(inside:K⊆conf n):
    ∀ᶠ k:ℕ in atTop,∀x∈K,∀p q:Viewers F,∀v:MaxwellSlots C d,
      ‖iteratedFDeriv ℝ j (measured F p (X.U k) v (X.r k)) x-
        iteratedFDeriv ℝ j (measured F q (X.U k) v (X.r k)) x‖≤(X.r k)^3*JetSalary.salary B v:=by
  have bank:∀ᶠ k:ℕ in atTop,∀t:(i:Fin n)→I i,∀x∈K,∀p q:Viewers F,
      ‖iteratedFDeriv ℝ j (measured F p (X.U k) (fun i=>B i (t i)) (X.r k)) x-
        iteratedFDeriv ℝ j (measured F q (X.U k) (fun i=>B i (t i)) (X.r k)) x‖≤(X.r k)^3:=
    Filter.eventually_all.mpr fun t=>(SparsePhases.original F X first J leading simple Q foundation d (fun i=>B i (t i)) j compact inside).2
  filter_upwards [bank] with k earned x hx p q v
  exact balance F X d j k x (inside hx) p q B v _ fun t=>earned t x hx p q

end YM.Existence.SelectedJets.MovingJets
end

noncomputable section
namespace YM.Existence.SelectedJets.SelectedStress
open Function Filter Set MeasureTheory Spec Extraction Table Maxwell Maxwell.Free
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato Table
open PhysMS.Frame
open scoped Topology BigOperators Classical

open scoped Matrix

open StressRows

variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}

open StressMenus

theorem original (F:Final C f S)(X:Scaling S)(first:Pert.FirstExtension F X)
    (J:ℝ→PhysMS.tower S)(leading:Leading F J)(simple:G.Simple)
    (Q:OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(foundation:OPE.Orbits.Foundation F Q)
    {n:ℕ}(q:Fin n→(Bel C.book).Tag)(marks:Fin n→Bool)(ab:Fin n→Axis×Axis)(j:ℕ)
    {K:Set (Points n)}(compact:IsCompact K)(inside:K⊆conf n){ε:ℝ}(pos:0<ε):
    ∀ᶠ k:ℕ in atTop,∀x∈K,∀p:Viewers F,
      ‖iteratedFDeriv ℝ j (fun y=>S.useAt (spectator F p) (X.r k • y)
          (Pert.scaledPhysical X F.sector.energy k q marks ab)) x-
        iteratedFDeriv ℝ j (Ward.disc (Pert.freeWithStress C.labels q marks ab)) x‖≤ε:=by
  obtain ⟨D,B,buyer⟩:=StressMenus.original C
  obtain ⟨V,posV,income⟩:=buyer F X first q marks ab
  have wallet:=MovingJets.original F X first J leading simple Q foundation (fun i=>StressMenus.height (q i) (marks i))
    (fun i=>StressMenus.basis B (q i) (marks i)) j compact inside
  have cst:Tendsto (fun _:ℕ=>V) atTop (𝓝 V):=tendsto_const_nhds
  have tail:Tendsto (fun k:ℕ=>(X.r k)^3*V) atTop (𝓝 0):=by simpa using (X.drips.pow 3).mul cst
  have tiny:=tail.eventually_lt_const (half_pos pos)
  have mean:=first.jets n j q marks ab compact inside (half_pos pos)
  filter_upwards [wallet,income,tiny,mean] with k bank paid small measured
  intro x hx p
  have back:=bank x hx p none (fun i=>StressMenus.pupil F X (q i) (ab i) k (marks i))
  rw [StressEntry.original F X k q marks ab p,StressEntry.original F X k q marks ab none] at back
  have gap:=back.trans (mul_le_mul_of_nonneg_left paid (pow_nonneg (X.positive k).le 3))
  let A:=iteratedFDeriv ℝ j (fun y=>S.useAt (spectator F p) (X.r k • y) (Pert.scaledPhysical X F.sector.energy k q marks ab)) x
  let M:=iteratedFDeriv ℝ j (fun y=>Ward.disc (Pert.scaledPhysical X F.sector.energy k q marks ab) (X.r k • y)) x
  let E:=iteratedFDeriv ℝ j (Ward.disc (Pert.freeWithStress C.labels q marks ab)) x
  change ‖A-E‖≤ε
  change ‖A-M‖≤(X.r k)^3*V at gap
  have m:‖M-E‖≤ε/2:=measured x hx
  have step:‖A-E‖≤‖A-M‖+‖M-E‖:=by simpa only [dist_eq_norm] using dist_triangle A M E
  linarith

end YM.Existence.SelectedJets.SelectedStress
end

noncomputable section
namespace YM.Existence.SelectedJets
open Function Filter Set Spec OPE Climb
open scoped Topology

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}

theorem ofTrace (F : Final C f S) (X : Scaling S) (first : Pert.FirstExtension F X)
    (simple : G.Simple) (Q : OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (foundation : OPE.Orbits.Foundation F Q) (trace : Trace.Target.Result.{0} F simple)
    {n : ℕ} (q : Fin n → (Bel C.book).Tag) (marks : Fin n → Bool)
    (ab : Fin n → Axis × Axis) (j : ℕ) {K : Set (Points n)} (compact : IsCompact K)
    (separated : K ⊆ conf n) {ε : ℝ} (pos : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ x ∈ K, ∀ p : Viewers F,
      ‖iteratedFDeriv ℝ j (fun y => S.useAt (spectator F p) (X.r k • y)
          (Pert.scaledPhysical X F.sector.energy k q marks ab)) x -
        iteratedFDeriv ℝ j (Ward.disc (Pert.freeWithStress C.labels q marks ab)) x‖ ≤ ε := by
  obtain ⟨H, Z, l, bliss, _⟩ := trace.stress
  obtain ⟨J, _, _, leading, _⟩ := PhysMS.Frame.base_stage simple F H bliss
  exact SelectedStress.original F X first J leading simple Q foundation q marks ab j compact separated pos

end YM.Existence.SelectedJets
end
