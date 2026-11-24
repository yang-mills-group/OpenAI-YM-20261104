import YM.RG11Proof.Fields.Enlarge
/-!
# One compatible nested choice of graded leading physical field bases

Valid even before any comparison to identify W or MS coefficients. Never
presumes interaction-null closure merely by using the separated quotient at
the free leading term.
-/
set_option autoImplicit false
set_option maxHeartbeats 150000
noncomputable section
namespace YM.RG11.Fields
open PowerSeries YM.RG11.Jets Function Set Labels Maxwell YM.Pert.Position Extra.FD MvPolynomial YM.Pert.RawLabels Horizon
open scoped Classical BigOperators ContDiff
variable {G:Gauge}{F:Frames G}{d e:ℕ}
namespace Basis

lemma signed_pure (M:Adapted F d)(s:Signed){i j:M.toBasis.J}(he:M.w i ≠ M.w j): M.toBasis.Hmat s i j=0:=by
  change (M.b.equivFun (Pert.Rigid.wear F d s (M.b i)) j).re=0
  rw [Pert.Rigid.wear_ride, pure_read M (rotation_pure F _ _ (M.alive i)) _ he.symm]; rfl
end Basis

lemma up_ride (h:e ≤ d) (s : Ortho) (v:E F e) : rideO F s d (up F h v) = up F h (rideO F s e v):=by
  apply writes_inj F d
  change writes F d (ride F s d _) = writes F d (up F h (ride F s e v))
  rw [ride_at,up_write,up_write,ride_at]
namespace Adapted
variable {B:Adapted F e}{D:Adapted F d}{f:B.toBasis.J↪ D.toBasis.J}{h:e ≤ d}
namespace Gives
lemma compatible (H : Gives B D h f) (s:Signed) : Horizon.take f (D.toBasis.Hmat s)=B.toBasis.Hmat s :=by
  ext i j
  let V := B.toBasis; let W:=D.toBasis
  change (D.b.equivFun (Pert.Rigid.wear F d s (D.b (f i))) (f j)).re=(B.b.equivFun (Pert.Rigid.wear F e s (B.b i)) j).re
  rw [H,Pert.Rigid.wear_ride,Pert.Rigid.wear_ride,up_ride]
  let v := rideO F s.ortho e (B.b i)
  suffices D.b.equivFun (up F h v) (f j)=B.b.equivFun v j from congrArg Complex.re this
  conv_lhs=>rw [← B.b.sum_equivFun v,_root_.map_sum,_root_.map_sum]
  simp_rw [Finset.sum_apply,_root_.map_smul,← (show ∀ i,_=up F h (B.b i) from H), Pi.smul_apply,Module.Basis.equivFun_self]
  classical simp

private theorem guard_eq (B:Adapted F e): B.toBasis.guard=(Constraints.position B.unitIndex (fun i=> (B.w i).1) B.toBasis.Hmat):=by
   have h:B.toBasis.guard.vary=(Constraints.position B.unitIndex (fun i=> (B.w i).1) B.toBasis.Hmat).vary:=SetLike.ext fun i=>exactGuard B i
   revert h; cases B.toBasis.guard; cases Constraints.position B.unitIndex (fun i=> (B.w i).1) B.toBasis.Hmat; simp

theorem unit (H : Gives B D h f): f B.unitIndex=D.unitIndex:=by
  apply D.b.injective
  rw [H,B.unitAt,D.unitAt]; apply writes_inj F d; rw [up_write,writes_unit,writes_unit]

theorem coherent (H : Gives B D h f): Horizon.Coherent f B.toBasis.guard D.toBasis.guard:=by
  rw [guard_eq B, guard_eq D, ←funext (H.compatible)]
  apply Coherent.of_position _ _ _ H.unit
  · intro s i j hj; apply Basis.signed_pure; intro hu; apply hj; apply H.retain; rw [←hu,H.weights]; exact B.heights i
  · exact fun j=> congrArg Prod.fst (H.weights j)
  exact fun i j H₁ => H.retain j (H₁.trans (B.heights i))
end Gives
end Adapted

section fixed
variable (F)
/-- Noncomputable but pinned by a single choice on F, no regulator or phase
data. `tower F d` can be announced together at all d. (A MS insertion lift or
physical schedule may still act on these by a fixed orientation matrix; use an
adapter.) -/
def tower (n:ℕ) : Adapted F n :=
  match n with
  |0=>eachBasis F 0
  |n+1=> Classical.choose ((tower n).after (Nat.le_succ n))

private theorem lifts (n:ℕ):∃ f:(tower F n).toBasis.J↪(tower F (n+1)).toBasis.J, (tower F n).Gives (tower F (n+1)) (Nat.le_succ n) f:= Classical.choose_spec ((tower F n).after (Nat.le_succ n))
private def goes (n:ℕ):= Classical.choose (lifts F n)
private theorem going (n:ℕ) : Adapted.Gives (tower F n) (tower F (n+1)) (Nat.le_succ n) (goes F n):= Classical.choose_spec (lifts F n)

private abbrev J(n:ℕ):= (tower F n).toBasis.J

theorem joint (n m:ℕ) (h:n ≤ m): ∃ f:J F n ↪ J F m, (tower F n).Gives (tower F m) h f:=by
  rcases Nat.exists_eq_add_of_le h with ⟨k,rfl⟩
  induction k with
  | zero => exact ⟨Embedding.refl _, fun i=> (up_self F _).symm⟩
  | succ k ih=>
    obtain ⟨g,hg⟩ := ih (Nat.le_add_right ..)
    exact ⟨g.trans (goes F (n+k)), Adapted.Gives.paths hg (going F _)⟩

def rise {n m:ℕ}(h:n ≤ m): (tower F n).toBasis.J↪(tower F m).toBasis.J:=Classical.choose (joint F n m h)
theorem basis_rise {n m:ℕ}(h:n ≤ m): Adapted.Gives (tower F n) (tower F m) h (rise F h) := Classical.choose_spec (joint F _ _ h)

theorem rises_stack {i j k:ℕ}(h:i ≤ j)(ht:j ≤ k): (rise F h).trans (rise F ht)=rise F (h.trans ht):=by
   apply Embedding.ext; intro t; apply (tower F k).b.injective; exact ((Adapted.Gives.paths (basis_rise F h) (basis_rise F ht)) t).trans ((basis_rise F (h.trans ht) t).symm)

theorem rises_self {i} : rise F (n:=i) le_rfl=Embedding.refl _ := Embedding.ext fun t=>
   (tower F i).b.injective ((basis_rise F (n:=i) le_rfl t).trans (up_self F _))

def asMesh (A B : (i:ℕ)→ArrayAt (tower F (6+i)).toBasis.J ℝ form): Horizon.Mesh ℝ form where
  J n:=(tower F (6+n)).toBasis.J
  count n:=inferInstanceAs (Fintype (J F (6+n)))
  requests n := (tower F (6+n)).toBasis.guard
  rise h:=rise F (Nat.add_le_add_left h 6)
  same _:= rises_self F
  together _ _:= rises_stack ..
  A:=A
  B:=B
-- Provide `up`-compatible array inputs in Steady on THIS type.
end fixed
end YM.RG11.Fields
