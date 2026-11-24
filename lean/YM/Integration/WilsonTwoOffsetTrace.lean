import YM.Integration.WilsonOffsetTraceHistory

/-! Two distinct children of the actual Wilson block are compared before
integration against the same nonlinear exterior at the actual upper cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonTwoOffsetTrace
open Function Filter MeasureTheory Lattice Wilson RG Source Push.GridApprox
open WilsonOffsetTraceHistory WilsonTranslatedFactory
open scoped Classical
variable {G : Gauge} {C : Family G} (H : C.Makes) {d N p m : ℕ}

def saw (hm : m<N) (z : Site (C.side (m+1) p)) (v : C.label d) :=
  let S:=C.path.levels.clock.op m p
  (fun V=>((C.S.block m).val:ℂ)^d * S.push (C.path.β N p (m+1)) (material H hm z v) V -
    material H hm.le (S.ratio.parent z) v V)

def pair (hm : m<N) (z : Site (C.side (m+1) p)) (v : C.label d) :=
  let S:=C.path.levels.clock.op m p
  (fun U=> initial (C.localSection d) C.path N p v (anchor C.S p hm z) U -
    initial (C.localSection d) C.path N p v (anchor C.S p hm.le (S.ratio.parent z)) U)

omit H in
theorem live (hm : m<N) (z : Site (C.side (m+1) p)) (v : C.label d) : Continuous (pair hm z v) :=
  (continuous_const.smul ((C.localSection d).continuous_places _ _)).sub
    (continuous_const.smul ((C.localSection d).continuous_places _ _))

omit H in
private theorem suffix (i : ℕ) (q : m+1 ≤ i) (f : Config G (C.side m p)→ℂ) :
    backTo C.path N p q (back (C.path.levels.clock.op m p) (C.path.β N p (m+1)) f) =
      backTo C.path N p (m.le_succ.trans q) f := by
  induction i,q using Nat.le_induction with
  | base => rw [backTo_self,backTo_next C.path N p (le_refl m),backTo_self]
  | succ i q ih => rw [backTo_next C.path N p q,backTo_next C.path N p (m.le_succ.trans q),ih]

omit H in
private theorem bundled {X : Type*} [MeasurableSpace X] {μ : Measure X} {u f : X→ℂ}
    (hu : Integrable u μ) (hf : Envelope f) : Integrable (fun x=>u x*f x) μ :=
  hu.mul_bdd hf.meas.aestronglyMeasurable (Eventually.of_forall hf.cost.choose_spec)

omit H in
private theorem engineer : ((C.S.block m).val:ℂ)^d * (C.S.a (m+1):ℂ)^d=(C.S.a m:ℂ)^d := by
  rw [mul_comm,←mul_pow,C.S.a_step,Complex.ofReal_div,Complex.ofReal_natCast]
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (C.S.block m).pos.ne')]

theorem physical (hr : C.ref d ≤ m) (hm : m<N) (z : Site (C.side (m+1) p)) (v : C.label d)
    (F : Config G (C.side m p)→ℂ) (hf : Envelope F) :
    (partition G (C.side N p) (C.beta N p):ℂ)⁻¹ * (∫ V, saw H hm z v V * F V ∂prior G _) =
      (C.S.a m:ℂ)^d * moment (C.beta N p) (fun U=>pair hm z v U * backTo C.path N p hm.le F U) := by
  let S:=C.path.levels.clock.op m p
  let β:=C.path.β N p (m+1)
  let K:=C.path.levels.transition_mass m p β
  let z':=S.ratio.parent z
  let A:=material H hm z v
  let B:=material H hm.le z' v
  let f:=back S β F
  let D:=backTo C.path N p hm.le F
  have hD : Envelope D := backTo_env C.path N p hm.le hf
  have hf' : Envelope f := back_env K hf
  have ha:=integrable H hm (hr.trans m.le_succ) z v
  have hb:=integrable H hm.le hr z' v
  have outA := interval H (hr.trans m.le_succ) hm z v hf'
  have outB := interval H hr hm.le z' v hf
  have dual := back_dual K hf A ha
  have sa := suffix (C:=C) (N:=N) N hm F
  dsimp only [f] at outA
  rw [sa] at outA
  have term (o:Site (C.side N p)) : Integrable (fun U=>
      ((C.path.rep N p N).eval U:ℂ)*initial (C.localSection d) C.path N p v o U*D U) (prior G _) := by
    rw [(H.wilson.starts N p).2]
    apply bundled _ hD
    apply (Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _))
    exact (Complex.continuous_ofReal.comp (bare_cont _)).mul (continuous_const.smul ((C.localSection d).continuous_places _ _))
  have comb : (∫ V, saw H hm z v V * F V ∂prior G _) = (C.S.a m:ℂ)^d *
      ∫ U, ((C.path.rep N p N).eval U:ℂ)*pair hm z v U*D U ∂prior G _ := by
    unfold saw
    change (∫ V, (((C.S.block m).val:ℂ)^d * S.push β A V - B V)*F V ∂prior G _) = _
    let aa (V : Config G (C.side m p)):=S.push β A V *F V
    let bb (V : Config G (C.side m p)):=B V*F V
    have ia : Integrable (fun V=>((C.S.block m).val:ℂ)^d * aa V) (prior G _) :=
      Integrable.const_mul (bundled (S.push_integrable K A ha) hf) _
    have ib : Integrable bb (prior G _):= bundled hb hf
    simp only [sub_mul,mul_assoc]
    change (∫ V, (((C.S.block m).val:ℂ)^d * aa V) - bb V ∂prior G _) = _
    rw [integral_sub ia ib,integral_const_mul]
    dsimp only [aa,bb]
    rw [dual]
    change ((C.S.block m).val:ℂ)^d*(∫ U,A U * f U ∂prior G _) - (∫ V,B V*F V ∂prior G _) = _
    rw [outA,outB,←mul_assoc,engineer]
    rw [←mul_sub,←integral_sub (term _) (term _)]
    congr 1; apply integral_congr_ae; filter_upwards with U
    unfold pair; ring
  rw [comb,moment_formula _ _ (((Envelope.compactC (live hm z v)).mulC hD).integrableC _),
    (H.wilson.starts N p).2]
  simp only [mul_assoc]
  change _ = _ * (_ * ∫ U, _ ∂prior G _) 
  rw [mul_left_comm]

end YM.Integration.WilsonTwoOffsetTrace
