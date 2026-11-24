import YM.Integration.WilsonOffsetFittedPrimary
import YM.Integration.WilsonOffsetProjectedInterior

/-! On the actual probability at every physical step, the displacement of
the measured primary loses only its fixed finite norm. At the terminal
entry this prices the entire centered source; at any other entry the
explicit signed failed-mask, soft and hard fields stay inside the posterior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetCompensatedGraph
open Function MeasureTheory Filter Lattice RG Wilson Labels Source
open PhysicalNext.Repeat.Legato WilsonOffsetConditionalCharge WilsonOffsetProjectedInterior
open WilsonOffsetFittedPrimary WilsonTwoOffsetTrace
open scoped Classical BigOperators
variable {G:Gauge}

theorem first (R:Run G) (hG:G.Simple) (d:ℕ) :
    ∀ᶠ m:ℕ in atTop, ∀ (p k:ℕ) (v:R.family.label d) (z:Site (R.family.side (m+1) p))
      (V:Config G (R.family.side m p)) (W Z:(R.family.labels.level d).Index → Bool → ℝ),
      let S:=R.family.path.levels.clock.op m p
      let e:=S.ratio.embed (S.ratio.parent z)
      due R (m+1) p m d k z V W → due R (m+1) p m d k e V Z →
      ‖saw (C:=R.family) R.makes (Nat.lt_succ_self m) z v V/((R.family.path.rep (m+1) p m).eval V:ℂ)-
        quote R d m v W Z‖ ≤ (∑i,‖v i‖)*(Next.SectorChange.coupling (R.family.path.β (m+1) p (m+1)))^k:=by
  filter_upwards [WilsonOffsetFittedPrimary.paid R hG d,eventually_ge_atTop (R.family.ref d)] with m paid hr p k v z V W Z
  dsimp only
  intro left right
  let S:=R.family.path.levels.clock.op m p
  let e:=S.ratio.embed (S.ratio.parent z)
  let P:=R.family.path.rep (m+1) p (m+1)
  let x:=(R.family.labels.level d).scaled (R.family.path.levels.clock.threshold (m+1))⁻¹ v
  have field : forward (C:=R.family) R.makes (N:=m+1) (Nat.lt_succ_self m) z v =
      fun U=>(R.family.localSection d).places x z U-(R.family.localSection d).places x e U :=
    funext (fun U=>born_difference (C:=R.family) R.makes (hr.trans m.le_succ) z v U)
  change ‖saw (C:=R.family) R.makes (Nat.lt_succ_self m) z v V/((R.family.path.rep (m+1) p m).eval V:ℂ)-_‖ ≤ _
  rw [observed (C:=R.family) (N:=m+1) (m:=m) R.makes hr (Nat.lt_succ_self m) z v V,field]
  exact paid (m+1) p (Nat.lt_succ_self m) v k z e V W Z left right

theorem interior (R:Run G) (hG:G.Simple) (d:ℕ) :
    ∀ᶠ m:ℕ in atTop, ∀ N p, (hm:m<N) → ∀ (k:ℕ) (v:R.family.label d)
      (z:Site (R.family.side (m+1) p)) (V:Config G (R.family.side m p))
      (W Z:(R.family.labels.level d).Index → Bool → ℝ),
      let S:=R.family.path.levels.clock.op m p
      let e:=S.ratio.embed (S.ratio.parent z)
      let Q:=(R.family.factory d N p).entries (m+1) v
      let v₀:=(R.family.labels.level d).core Q.x
      let P:=R.family.path.rep N p (m+1)
      due R N p m d k z V W → due R N p m d k e V Z →
      ‖saw (C:=R.family) R.makes hm z v V/((R.family.path.rep N p m).eval V:ℂ)-
        quote R d m v₀ W Z-((R.family.S.block m).val:ℂ)^d*
          conditional S P V (gap (C:=R.family) (rest (C:=R.family) (N:=N) (m:=m) v) z)‖ ≤
        (∑i,‖v₀ i‖)*(Next.SectorChange.coupling P.beta)^k:=by
  filter_upwards [WilsonOffsetFittedPrimary.paid R hG d,eventually_ge_atTop (R.family.ref d)] with m paid hr N p hm k v z V W Z
  dsimp only
  intro left right
  let S:=R.family.path.levels.clock.op m p
  let e:=S.ratio.embed (S.ratio.parent z)
  let P:=R.family.path.rep N p (m+1)
  let F:=R.family.labels.level d
  let v₀:=F.core (((R.family.factory d N p).entries (m+1) v).x)
  let θ:=R.family.path.levels.clock.threshold (m+1)
  have hθ:P.p.threshold=θ:=by
    rw [show P.p=R.family.path.levels.budget (m+1) from (R.makes.wilson.represents N p (m+1) hm).vac]
    rfl
  have poly : gap (C:=R.family) (primaryAt (C:=R.family) (N:=N) (m:=m) v) z=
      fun U=>(R.family.localSection d).places (F.scaled θ⁻¹ v₀) z U -
        (R.family.localSection d).places (F.scaled θ⁻¹ v₀) e U :=by
    unfold gap primaryAt payload
    rw [hθ]
  change ‖saw (C:=R.family) R.makes hm z v V/((R.family.path.rep N p m).eval V:ℂ)-quote R d m v₀ W Z-
    ((R.family.S.block m).val:ℂ)^d*conditional S P V (gap (C:=R.family) (rest (C:=R.family) (N:=N) (m:=m) v) z)‖ ≤ _
  have drop (a b q:ℂ):a+b-q-b=a-q:=by ring
  rw [WilsonOffsetProjectedInterior.subtract (C:=R.family) R.makes hr hm z v V,poly,mul_add,drop]
  exact paid N p hm v₀ k z e V W Z left right

end YM.Integration.WilsonOffsetCompensatedGraph
