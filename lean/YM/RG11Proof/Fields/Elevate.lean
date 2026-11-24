import YM.RG11Proof.Fields.Profile

/-! Canonical horizon lifts via exact free writing. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.RG11.Fields
open PowerSeries YM.RG11.Jets Function Set Labels Maxwell YM.Pert.Position Extra.FD MvPolynomial YM.Pert.RawLabels
open scoped Classical BigOperators ContDiff
variable {G : Gauge}(F:Frames G)
variable {d e n:ℕ}

/-- Use the exact horizon lift (free Label spaces ALSO before a choice of
physical orientation). Agrees with known rises. -/
def up (h:e ≤ d): E F e →ₗ[ℂ] E F d:= enroll F d ∘ₗ raiseLabel G h ∘ₗ physicalLabel F e

theorem up_write (h:e ≤ d)(v:E F e): writes F d (up F h v)=writes F e v:=by
  let q := physicalLabel F e v
  change writes F d (enroll F d (raiseLabel G h q))=_
  rw [enroll_write]
  trans writes F e (enroll F e q)
  · exact (enroll_write F e q).symm
  rw [show enroll F e q = v from physical_round F v]

theorem up_inject (h:e ≤ d): Injective (up F h):=fun x y he=> writes_inj F _ (by simpa [up_write] using! congrArg (writes F d) he)

@[simp] theorem up_self (v:E F d): up F le_rfl v=v:= writes_inj F _ (up_write F _ v)

theorem up_enroll (h:e ≤ d) (v:Label G e) : up F h (enroll F e v)= enroll F d (raiseLabel G h v):= by
  apply writes_inj F d; rw [up_write,enroll_write,enroll_write]; rfl

theorem up_up (h:n ≤ e)(he:e ≤ d)(v:E F n): up F he (up F h v)=up F (le_trans h he) v:=writes_inj F _ (by simp only [up_write])

-- `lower` also includes the whole current horizon.
theorem staircase (h : e ≤ d) : LinearMap.range (up F h)=lower F e d:= by
  ext p
  constructor
  · rintro ⟨v,rfl⟩
    let Q:=physicalLabel F e v
    let L:=raiseLabel G h Q
    change enroll F d L ∈ _
    exact ⟨⟨L.val,(show L.val∈localFields G e from Q.property),L.property⟩,rfl⟩
  rintro ⟨q,rfl⟩
  exact ⟨enroll F e ⟨q.val,q.property.1⟩,up_enroll F h _⟩

lemma top_step (p:E F d): p∈lower F d d:= by rw [← staircase F le_rfl]; exact ⟨p,up_self F p⟩

-- Exact off-origin readings reuse in proof; no claims on tested schedule errors.
lemma writes_pair (x:Points n) (p : Fin n→ E F d):
    visible F d x p= Maxwell.Wick.moment G x (fun i=>writes F d (p i)):= writes_eval F x (fun i=>⟨d,p i⟩)

lemma up_moment (h:e ≤ d)(x:Points n)(p:Fin n→E F e):
    visible F d x (up F h ∘ p)=visible F e x p:=by simp only [writes_pair, Function.comp_apply,up_write]

lemma up_buffer {l:ℕ} (z : Buffer F d) (h:l ≤ d) (v:E F l): z.val (up F h v) ∈ lower F l d:=by
  obtain rfl|hl:=eq_or_lt_of_le h
  · exact top_step ..
  exact z.property.2.1 _ hl _ ((staircase F h) ▸ (show up F h v∈LinearMap.range (up F h) from ⟨v,rfl⟩))
end YM.RG11.Fields
