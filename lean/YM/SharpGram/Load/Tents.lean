import YM.SharpGram.Load.Sail

/-!
# True aligned measuring frames

Inversion on free Field (so true Maxwell rank basis). Costs simultaneously
hold. This is a genuine physical relative basis bound; read BEFORE using
RG12/Fits across-length hypothesis. No distances asserted outside the
specified Mantle.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Load
open Function Filter Set Table Climb Analysis Org Extraction Spec Next.UVStress Lenses
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G: Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S}
local notation "V"=> F.sector.derivatives
local notation "V'"=> Maxwell.Free.scheme C.labels
local notation "σ" => Maxwell.Free.spin_free C.labels
local notation "E" => Maxwell.Free.gear C.labels
local notation "α" => F.sector.turns
local notation "S'"=> (Bel C.book)
local notation "T" => F.phase.transport
variable {u : Filter (ℕ×ℕ)}

section invert
private lemma near_dist {X:Type*}[NormedAddCommGroup X] [NormedSpace ℂ X]
    (f:ℕ → X→L[ℂ] X) (h:Tendsto f atTop (𝓝 1)) :∀ᶠ i in atTop, ‖f i-1‖ ≤ 1 := by
  filter_upwards [(Metric.tendsto_nhds (a:=1) (u:=f)).mp h 1 one_pos] with i hi
  rw [← dist_eq_norm];exact hi.le
private lemma started {X:Type*}[NormedAddCommGroup X] [NormedSpace ℂ X][CompleteSpace X]
    (f:ℕ → X→L[ℂ] X)(h:Tendsto f atTop (𝓝 1)) : ∀ᶠ i in atTop, IsUnit (f i):= by
  exact h.eventually (Units.isOpen.mem_nhds isUnit_one)
private lemma ring_rev {X:Type*}[NormedAddCommGroup X] [NormedSpace ℂ X][CompleteSpace X]
    (f:ℕ → X→L[ℂ] X)(h:Tendsto f atTop (𝓝 1)) : Tendsto (fun n=> Ring.inverse (f n)) atTop (𝓝 1):= by
    rw [← Ring.inverse_one (X→L[ℂ] X)]; exact (NormedRing.inverse_continuousAt (1 : (X→L[ℂ] X)ˣ)).tendsto.comp h
private lemma twice {X:Type*}[NormedAddCommGroup X] [NormedSpace ℂ X]
     (f:X→L[ℂ] X)(h: ‖f-1‖ ≤ 1)(x:X): ‖f x‖ ≤ 2*‖x‖ := by
    have he : ‖f x-x‖ ≤ ‖x‖:= ((f-1).le_opNorm x).trans ((mul_le_mul_of_nonneg_right h (norm_nonneg _)).trans_eq (one_mul _))
    refine (norm_le_norm_sub_add (f x) x).trans ?_
    linarith only [he]
end invert
variable (B : Lenses.Mantle F u)
local notation "A"=> B.lens
noncomputable def tent (k d:ℕ):= if h:IsUnit (shift B k d) then (Spin.unit_shape _ h).choose.trans (A k d) else A k d

private lemma tent_eq {k d:ℕ} (h:IsUnit (shift B k d))(x:(Bel C.book).Field d) : tent B k d x=A k d (shift B k d x) := by
    unfold tent; rw [dif_pos h,LinearEquiv.trans_apply]; exact congr_arg _ (LinearMap.congr_fun (Spin.unit_shape _ h).choose_spec x)
private lemma tent_rev {k d:ℕ} (h:IsUnit (shift B k d))(x:S.Field d) : (tent B k d).symm x= Ring.inverse (shift B k d) ((A k d).symm x) := by
    let X:=Spin.Mat ((Bel C.book).Field d); let f:=shift B k d
    apply (tent B k d).injective; rw [LinearEquiv.apply_symm_apply,tent_eq B h]
    change x=A k d ((f*Ring.inverse f) ((A k d).symm x))
    rw [Ring.mul_inverse_cancel ..]; exact (LinearEquiv.apply_symm_apply ..).symm
    exact h
lemma tensor_edge {k d : ℕ} (h:IsUnit (shift B k d))(v :Ortho)(x:(Bel C.book).Field d) :
    tent B k d ((E).act d v x) = (α).act d v (tent B k d x):= by
  rw [tent_eq B h,tent_eq B h]; apply (A k d).symm.injective
  rw [LinearEquiv.symm_apply_apply]; exact DFunLike.congr_fun (shift_comm B k d v) x
variable (hg:OPE.Services C f S)
include hg
section
lemma tented (d:ℕ) : ∀ᶠ k in atTop, IsUnit (shift B k d):= started _ (sails B hg d)
lemma obtuse (d:ℕ) : ∀ᶠ k in atTop, ∀ g x, tent B k d ((E).act d g x) = (α).act d g (tent B k d x) := (tented B hg d).mono fun _ hk => tensor_edge B hk
lemma authored (D:ℕ) : ∀ᶠ k in atTop, Extra.WeakScaling.Graded V V' F.room.kernel.spin σ (tent B k) D:=by
    filter_upwards [B.aged D
    , eventually_all.mpr (fun i: Fin (D+1)=> (tented B hg i).and ((shift_real B i).and (shift_fixes B i))),
      eventually_all.mpr (fun i: Fin (D+1)=> eventually_all.mpr (fun j: Fin (D+1)=> eventually_all.mpr (fun h:i.val ≤ j.val=> shift_filtered B h)))] with k hk hr hs
    replace hr : ∀ i≤D, IsUnit (shift B k i) ∧ (∀ x,shift B k i ((S').conj σ i x)=(S').conj σ i (shift B k i x)) ∧ shift B k i ((S').unit i)=(S').unit i := fun i hi=> hr (⟨i,Nat.lt_succ_of_le hi⟩:Fin (D+1))
    constructor
    · intro i hi; obtain ⟨hx,hy,hz⟩ := hr i hi; obtain ⟨hq,hl,hP⟩:= hk.1 i hi
      refine ⟨?_,?_,?_⟩
      · intro g x; change tent B k i ((S').mirror σ i g x)= _
        rw [← (Maxwell.Free.gear_laws C.labels).signed, tensor_edge B hx,(T).spots.signed]; rfl
      · intro x; change tent B k i _ = Table.conj _ _ _ (tent B k i x)
        rw [tent_eq B hx,tent_eq B hx, hy]; exact hl _
      change tent B k i _= S.unit i; rw [tent_eq B hx,hz]; exact hP
    intro i j he hj x
    change tent B k j _=(V).rise he (tent B k i x)
    rw [tent_eq B (hr j hj).1,tent_eq B (hr i (he.trans hj)).1]
    rw [show shift B k j ((V').rise he x)=_ from hs ⟨_,Nat.lt_succ_of_le (he.trans hj)⟩ ⟨_,Nat.lt_succ_of_le hj⟩ he x]
    exact hk.2 _ _ he hj _
lemma seats {d:ℕ} {x:ℕ→(S').Field d}{v : (S').Field d}(hv:Tendsto x atTop (𝓝 v)) : Tendsto (fun k=> (B.lens k d).symm (tent B k d (x k))) atTop (𝓝 v):= by
    refine (Dash.arcing (sails B hg d) hv).congr' ?_
    filter_upwards [tented B hg d] with k hk
    rw [tent_eq B hk,LinearEquiv.symm_apply_apply]
lemma rent {d:ℕ} {x:ℕ→S.Field d} {y:(S').Field d} (hv:Tendsto (fun k=>(A k d).symm (x k)) atTop (𝓝 y)) : Tendsto (fun k => (tent B k d).symm (x k)) atTop (𝓝 y):= by
    refine (Dash.arcing (ring_rev _ (sails B hg d)) hv).congr' ?_; exact (tented B hg d).mono fun k hk => (tent_rev B hk _).symm

local notation "P"=> C.path.levels.clock.hatBeta
-- transferred version of Mantle.Costs, with explicit estimated extra factor 2 (absorbed in any budget).
theorem investors (d:ℕ) : ∀ᶠ k in atTop,
    (∀ x : S.Field d, ∃ (y : C.label d) (q : ℕ×ℕ → C.label d), S.project d y=x ∧ Tendsto q u (𝓝 y) ∧
       ∀ᶠ i in u, quota C d k i.1 i.2 (q i) ≤ 2*P k^Lenses.price d * C.S.a k ^ d * ‖(tent B k d).symm x‖) ∧
    ∀ (v : Filter (ℕ×ℕ)) (_ : v.NeBot) (_ : v ≤ u) (q : ℕ×ℕ → C.label d)(x : C.label d)(z:ℝ),
            (∀ᶠ i in v, quota C d k i.1 i.2 (q i) ≤ z) → Tendsto q v (𝓝 x) →
              ‖(tent B k d).symm (S.project d x)‖ ≤ 2*Lenses.bonus C d / C.S.a k ^ d * z := by
    filter_upwards [B.pricesD d,tented B hg d, near_dist _ (sails B hg d), near_dist _ (ring_rev _ (sails B hg d))] with k hk hz hQ hR
    constructor
    · intro x; obtain ⟨y,q,hy,ht,hq⟩:=hk.courtesy x; refine ⟨y,q,hy,ht,hq.mono fun i he=> he.trans ?_⟩
      have ha : (A k d).symm x=shift B k d ((tent B k d).symm x) := ((A k d).injective ?_)
      swap; rw [LinearEquiv.apply_symm_apply,← tent_eq B hz,LinearEquiv.apply_symm_apply]
      have hb:= twice (shift B k d) hQ ((tent B k d).symm x); rw [← ha] at hb
      exact (mul_le_mul_of_nonneg_left hb (show 0 ≤ P k^_ * C.S.a k^_ by apply mul_nonneg; exact pow_nonneg (zero_le_one.trans (C.path.levels.fits.delayed k).le) _; positivity [C.S.a_pos k])).trans_eq (by ring)
    intro v hc hv q x z hq ht
    rw [tent_rev B hz]; refine (twice _ hR _).trans ((mul_le_mul_of_nonneg_left (hk.outlet v hv q x z hq ht) zero_le_two).trans_eq ?_)
    ring
end
end YM.SharpGram.Load
