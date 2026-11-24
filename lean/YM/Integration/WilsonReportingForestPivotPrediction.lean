import YM.Integration.WilsonReportingForestRelative
import YM.MatchingR2.Top.Weather

/-! The remaining genuine free crossing bond and the actual, positive-mass
spring tag on the same forest configuration. The macro plaquette bill and the
sampled noise angle remain visible. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingForestPivots
open Lattice RG Wilson Tree OPE.Therm MSbar.Heath Bid Pressure Precision Filter PhysicalNext.Repeat.Legato
open WilsonPhysicalRegisteredForestAction
open scoped Classical
variable {G:Gauge} {c f:Side} {S:StepData c f}

/-- Local faces of the original tag predictor at the coarse parent of a genuine fine wire. -/
def predictorFaces (T:Forest S.ratio) (a:T.Free) : Finset (Face (Per f)) :=
  WilsonAxialWindow.cells (S.ratio.embed (S.ratio.parent a.val.1)) (macroR S.patch)

theorem predicted (T:Forest S.ratio) (a:T.Free) (cross:¬internal T a) (period:100*macroR S.patch≤f.val)
    (coarse:1<c.val) (u:T.Slice G) (t:S.Choices) (used:S.likelihood (T.drape u) t≠0) {τ:ℝ} (pos:0≤τ)
    (cold:T.drape u∈House.chilly (predictorFaces T a) τ) :
    let b:=(S.ratio.parent a.val.1,a.val.2)
    let Q:=S.prediction (T.drape u) t
    let h:=compass S.patch S.kernel G*(breeze S*τ)
    G.chord (u a*(Q b)⁻¹)≤h ∧ ∀V:Config G c,G.chord (u a*(V b)⁻¹)≤h+G.chord (V b*(Q b)⁻¹) := by
  intro b Q h
  have apart:S.ratio.parent a.val.1≠S.ratio.parent (a.val.1+step a.val.2):=cross
  have fee:port S b.1 (T.drape u)≤breeze S*τ:=by
    apply Work.E01.port_le S _ _ _ pos
    intro x live
    obtain ⟨z,hz⟩:=Finset.card_pos.mp live
    obtain ⟨iz,atx,_⟩:=Finset.mem_filter.mp hz
    have mem:x∈predictorFaces T a:=by
      rcases x with ⟨x,ax⟩
      change wrap f z+S.ratio.embed b.1=x at atx
      rw [←atx]
      exact WilsonAxialWindow.cell _ _ iz ax
    exact cold x mem
  have bound (V:Config G c):G.chord (u a*(V b)⁻¹)≤h+G.chord (V b*(Q b)⁻¹):=by
    have z:=(Work.E02.answer G S.patch.L S.patch.J S.kernel).choose_spec.2 c f S rfl rfl rfl period coarse
      T (T.drape u) (fun i hi=>T.on_tree u ⟨i,hi⟩) V a.val t
      (Pressure.wraps S t ((S.likelihood_pos _ _).lt_of_ne used.symm) b.1)
    unfold Cops at z
    simp only [T.off_tree,replica,if_neg apart,if_neg apart.symm,wire] at z
    exact z.trans (add_le_add_left (mul_le_mul_of_nonneg_left fee (weather_pos G S).le) _)
  refine ⟨?_,bound⟩
  simpa only [mul_inv_cancel,G.chord_one,add_zero] using bound Q

/-- On the actual before-period Wilson schedule, the specific fine reference
kept in the outer fibre is close to its genuine positive-mass tag predictor
up to the charged macro plaquettes. The distance to the held datum has one
further, literal spring noise term. -/
theorem sampled (R:Run G) : ∀ᶠ m:ℕ in atTop,∀per,
    let S:=R.family.path.levels.clock.op m per
    ∀(T:Forest S.ratio) (B:Finset T.Free) (e:T.Free) (cross:¬internal T e),
    let E:=moving T B
    let a:=pivot T e
    let b:=(S.ratio.parent a.val.1,a.val.2)
    ∀(v:({i:T.Free|i∉E}:Set T.Free)→G.El) (x:↥E→G.El) (t:S.Choices),
    let U:=restored T B v x
    let Q:=S.prediction U t
    let old:=v ⟨a,saved T B e cross⟩
    let τ:=cool R.family.path.levels (m+1)
    let h:=compass S.patch S.kernel G*(breeze S*τ)
    S.likelihood U t≠0→U∈House.chilly (predictorFaces T a) τ→
      G.chord (old*(Q b)⁻¹)≤h ∧ ∀V:Config G (R.family.side m per),G.chord (old*(V b)⁻¹)≤h+G.chord (V b*(Q b)⁻¹) := by
  filter_upwards [MatchingR2.Top.step_shape R.family.path] with m larger per
  dsimp only
  intro T B e cross v x t used good
  let a:=pivot T e
  let E:=moving T B
  let u:=(cut T E).symm (x*background T B v,v)
  have outside:=saved T B e cross
  have read:u a=v ⟨a,outside⟩:=by
    exact congrFun (congrArg Prod.snd ((cut T E).apply_symm_apply (x*background T B v,v))) ⟨a,outside⟩
  have crossed:¬internal T a:=by
    unfold internal a
    rw [pair_of]
    exact cross
  have since:=predicted T a crossed (larger per).2.1 (larger per).2.2 u t used
    (by unfold cool RG.Calendar.hatCoupling;positivity) good
  dsimp only at since
  rw [read] at since
  exact since

end YM.Integration.WilsonReportingForestPivots
