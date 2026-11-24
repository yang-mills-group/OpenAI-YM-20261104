import YM.Integration.WilsonTranslatedFactory
import YM.Push.GRID_APPROXIMATION.Iterate

/-! Exact transfer of a genuine translated Wilson coefficient against a common
nonlinear observable, in the finite physical Haar coordinates. The fine
coordinate is lifted only through the original block embeddings. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetTraceHistory
open Function Filter MeasureTheory Lattice RG Wilson Source Push.GridApprox
open WilsonTranslatedFactory
open scoped Classical
variable {G : Gauge} {C : Family G} (H : C.Makes) {d N p : ℕ}

def material {m : ℕ} (hm : m ≤ N) (z : Site (C.side m p)) (v : C.label d) :=
  (entry H hm z v).density z (C.localSection d) (C.path.rep N p m)

theorem integrable {m : ℕ} (hm : m ≤ N) (hr : C.ref d ≤ m) (z : Site (C.side m p))
    (v : C.label d) : Integrable (material H hm z v) (prior G (C.side m p)) := by
  obtain ⟨hf,hr'⟩ := based H hr hm z v
  exact ((entry H hm z v).envelope (C.localSection d) (H.wilson.represents N p m hm).good hr' hf).integrableC _

private theorem one {i : ℕ} (hr : C.ref d ≤ i) (hi : i < N) (o:Site (C.side i p))
    (v:C.label d) {F : Config G (C.side i p)→ℂ} (hf:Envelope F) :
    (∫ V, material H hi.le o v V * F V ∂prior G _) =
      ((C.S.block i).val:ℂ)^d * ∫ U, material H hi ((C.path.levels.clock.op i p).ratio.embed o) v U *
        back (C.path.levels.clock.op i p) (C.path.β N p (i+1)) F U ∂prior G _ := by
  let S:=C.path.levels.clock.op i p
  let β:=C.path.β N p (i+1)
  let X:=material H hi (S.ratio.embed o) v
  have eq : material H hi.le o v=((C.S.block i).val:ℂ)^d • S.push β X := transfer H hr hi o v
  rw [eq]
  simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,integral_const_mul]
  exact congrArg _ (back_dual (C.path.levels.transition_mass ..) hf X (integrable H hi (hr.trans i.le_succ) _ _))

private theorem scale {i : ℕ} :
    (C.S.a (i+1):ℂ)^d * ((C.S.block i).val:ℂ)^d=(C.S.a i:ℂ)^d := by
  rw [←mul_pow,C.S.a_step,Complex.ofReal_div,Complex.ofReal_natCast]
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (C.S.block i).pos.ne')]

theorem interval {k : ℕ} (hr : C.ref d ≤ k) (hk : k ≤ N) (z : Site (C.side k p)) (v : C.label d)
    {F:Config G (C.side k p)→ℂ} (hf:Envelope F) :
    (∫ V,material H hk z v V * F V ∂prior G _) = (C.S.a k:ℂ)^d * ∫ U,
      (C.path.rep N p N).eval U * initial (C.localSection d) C.path N p v (anchor C.S p hk z) U *
        backTo C.path N p hk F U ∂prior G _ := by
  let E (i : ℕ) (ki : k ≤ i) (hi : i ≤ N) := ∫ U,
    material H hi (anchor C.S p ki z) v U * backTo C.path N p ki F U ∂prior G _
  have start : anchor C.S p (le_refl k) z = z := by
    simp [anchor,Schedule.toDepth,Ratio.embed,Schedule.steps]
  have all (i : ℕ) (ki : k ≤ i) (hi : i ≤ N) :
      (C.S.a i:ℂ)^d * E k le_rfl hk = (C.S.a k:ℂ)^d * E i ki hi := by
    induction i,ki using Nat.le_induction with
    | base => rfl
    | succ i ki ih =>
      have step : E i ki (by omega) = ((C.S.block i).val:ℂ)^d * E (i+1) (by omega) hi := by
        dsimp only [E]
        rw [←anchor_next C.S p ki,backTo_next C.path N p ki]
        exact one H (hr.trans ki) hi _ v (backTo_env C.path N p ki hf)
      have old:=ih (show i ≤ N by omega)
      have az : (C.S.a i:ℂ)^d≠0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos i).ne')
      apply (mul_left_cancel₀ az)
      calc
        _ = (C.S.a (i+1):ℂ)^d*((C.S.a i:ℂ)^d*E k le_rfl hk) := by ring
        _ = _ := by rw [old,step]; rw [← scale (C:=C) (d:=d) (i:=i)]; ring
  have eq:=all N hk le_rfl
  have top : E N hk le_rfl = (C.S.a N:ℂ)^d * ∫ U,
      (C.path.rep N p N).eval U * initial (C.localSection d) C.path N p v (anchor C.S p hk z) U *
        backTo C.path N p hk F U ∂prior G _ := by
    unfold E material
    simp_rw [born H (hr.trans hk),mul_assoc,integral_const_mul]
  rw [top] at eq
  dsimp only [E] at eq
  rw [start,backTo_self] at eq
  apply mul_left_cancel₀ (pow_ne_zero d (Complex.ofReal_ne_zero.mpr (C.S.a_pos N).ne'))
  calc _ = _ := eq
       _ = _ := by ring

end YM.Integration.WilsonOffsetTraceHistory
