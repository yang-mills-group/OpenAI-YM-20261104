import YM.Integration.WilsonMacroscopicRichWatchLaw

/-! The finite normalized detector converges in operator norm on the genuine physical label space. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichWatchLabels
open Set Function Filter MeasureTheory Spec OPE OPE.Orbits Lattice Cells Wilson Next.UVStress
open WilsonMacroscopicRichWatchLaw WilsonMacroscopicRichWatchPlot WilsonMacroscopicRichFixedWatchSale
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}

def source (C:Family G)(h N p:ℕ):C.label h→ₗ[ℂ]ContinuousMap (Config G (C.side N p)) ℂ where
  toFun z:=⟨C.O N p z 0,C.continuousO N p h z 0⟩
  map_add' x y:=by ext U;exact congrFun (((C.linearO N p h 0).mk' _).map_add x y) U
  map_smul' t x:=by ext U;exact congrFun (((C.linearO N p h 0).mk' _).map_smul t x) U

def row (W:Watch C)(h:ℕ)(w:ℕ×ℕ):C.label h→ₗ[ℂ]ℂ:=
  (meter C W).comp (source C h w.1 w.2)

theorem read (W:Watch C)(h:ℕ)(w:ℕ×ℕ)(z:C.label h):
    row W h w z=C.numeric w.1 w.2 (Fin.cons (α:=fun _=>C.book.Token) ⟨h,z⟩ W.q) (W.cuts w.1 w.2):=by
  change meter C W (source C h w.1 w.2 z)=_
  rw [same,C.num]
  apply congrArg (moment (C.beta w.1 w.2))
  funext U
  rw [Fin.prod_univ_succ]
  rfl

theorem limits (F:Final C f S)(W:Watch C)(h:ℕ)(z:C.label h):
    Tendsto (fun w:ℕ×ℕ=>row W h w z) f.fuse (𝓝 (W.tester S h (S.project h z))):=by
  have target:S.read W.held (Fin.cons (α:=fun _=>C.book.Token) ⟨h,z⟩ W.q)=W.tester S h (S.project h z):=by
    rw [Watch.test_known,← S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) W.distinct]
    rw [Work.A01.comp_cons]
    rfl
  rw [←target]
  exact (W.single_lim ⟨h,z⟩ F.room.generic).congr (fun w=>(read W h w z).symm)

def hearing {a h:ℕ}(W:Fin a→Watch C)(D:(Fin a→ℂ)→L[ℂ]S.Field h)(w:ℕ×ℕ):C.label h→ₗ[ℂ]S.Field h:=
  D.toLinearMap.comp (LinearMap.pi (fun i=>row (calibrated S (W i)) h w))

theorem performed {a h:ℕ}(W:Fin a→Watch C)(D:(Fin a→ℂ)→L[ℂ]S.Field h)(w:ℕ×ℕ)(z:C.label h):
    hearing W D w z=D (heard (calibrated S ∘ W) w (C.O w.1 w.2 z 0)):=by
  apply congrArg D
  funext i
  exact same C _ (source C h w.1 w.2 z)

theorem original (F:Final C f S){a h:ℕ}(W:Fin a→Watch C)(D:(Fin a→ℂ)→L[ℂ]S.Field h)
    (fits:∀z,D (fun i=>(W i).tester S h z)=z):
    Tendsto (fun w=>(hearing W D w).toContinuousLinearMap) f.fuse
      (𝓝 (S.project h).toContinuousLinearMap):=by
  apply Dash.fit_plane
  intro z
  rw [← fits (S.project h z)]
  apply D.continuous.continuousAt.tendsto.comp
  apply tendsto_pi_nhds.mpr
  intro i
  change Tendsto (fun w:ℕ×ℕ=>row (calibrated S (W i)) h w z) f.fuse (𝓝 ((W i).tester S h (S.project h z)))
  simpa only [invariant] using limits F (calibrated S (W i)) h z

end YM.Integration.WilsonMacroscopicRichWatchLabels
