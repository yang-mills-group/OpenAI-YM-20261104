import YM.Integration.WilsonMeasuredFullPrimary

/-! The complete physical primary at any occupied root is fixed by the
original signed healthy germ. Both possible winding corrections have the
original exponentially small spatial bill, with either forced gallery. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredRankedGerm
open Filter Function Finset Lattice RG Wilson Source Labels Push.Local Extra.Histories
open ProjectorNext.Equivariance Trace.Physical Trace.Physical.Germ QuadraticLocal Marker RG3.Forms RG3.Primary
open scoped Classical Topology BigOperators
variable {G : Gauge} {n : Side} {V T ι : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    [Nonempty T] [Countable ι] {B : Census V} {o : V → Site n} {W : Rep G n}
    {d : ℕ} {F : Frame G d}

def wrapCost (F : Frame G d) (Y : Hol G) : ℝ := (Fintype.card F.Index : ℝ)*(germ_close F Y).choose

theorem wrapCost_nonneg (F : Frame G d) (Y : Hol G) : 0 ≤ wrapCost F Y :=
  mul_nonneg (Nat.cast_nonneg _) (germ_close F Y).choose_spec.1.le

theorem compare (Y : Hol G) (S : SectionData F) (sound:S.Sound Y) (y : Site n)
    (hu:∀ z∈S.stencil,∀ i:Axis,20*((z i).natAbs+1)≤n.val)
    (hd:d≤W.p.order) (hp:d≤W.p.power) (hs:∀ v,HasOrderAt (S.places v y) 1 d)
    (q r:Coefficient F n) {κ a b:ℝ}
    (fq:q.Format y Y W) (fr:r.Format y Y W) (qa:q.remBound y W κ a) (rb:r.remBound y W κ b)
    (same:q.density y S W =ᶠ[𝓝 1] r.density y S W) :
    (projection F Y W.p.threshold y q = projection F Y W.p.threshold y r) ∧
    F.coeffSize q.x ≤ F.coeffSize r.x + wrapCost F Y * wraps W.p n*(a+b) := by
  have formula:=intrinsic_at F Y S sound y hu hd hp hs q r fq fr ⟨κ,a,qa⟩ ⟨κ,b,rb⟩ same
  refine ⟨formula,?_⟩
  let C:=(germ_close F Y).choose
  have hq:=(germ_close F Y).choose_spec.2 W q fq qa hd hp
  have hr:=(germ_close F Y).choose_spec.2 W r fr rb hd hp
  have price:‖q.x-r.x‖ ≤ C*wraps W.p n*(a+b) := by
    calc
      _ ≤ ‖q.x-projection F Y W.p.threshold y q‖+‖projection F Y W.p.threshold y q-r.x‖ := by
        simpa only [dist_eq_norm] using dist_triangle q.x (projection F Y W.p.threshold y q) r.x 
      _ ≤ C*wraps W.p n*a+C*wraps W.p n*b := by
        exact add_le_add (by rw [norm_sub_rev q.x]; exact hq) (by rw [formula]; exact hr)
      _ = _ := by ring
  unfold Frame.coeffSize
  calc
    _ ≤ ∑ z, (‖r.x z‖ + C*wraps W.p n*(a+b)) := Finset.sum_le_sum (fun z _=>by
      have site:‖q.x z-r.x z‖ ≤ C*wraps W.p n*(a+b) :=
        (norm_le_pi_norm (q.x-r.x) z).trans price
      exact (norm_le_norm_add_norm_sub' (q.x z) (r.x z)).trans (add_le_add le_rfl site))
    _ = _ := by simp [Finset.sum_add_distrib,wrapCost,C]; ring

theorem regular (L : Gallery T ι o W B) {θ : V→ℝ} {κ reg hard b : ℝ}
    (hw:∀v,0<θ v) (divisor:0<κ) (valid:W.activities.ForcedFamily W.p)
    (soft:L.E.Paid θ W.p.B (W.p.supportExponent+2) reg)
    (hardPaid:L.K.Paid θ W.p.B W.p.supportExponent hard)
    (x:T) (v:V) (Y:Hol G) (S:SectionData F) {μ:ℝ} (he:Readable Y S W.p n μ)
    (hu:∀ z∈S.stencil,∀ i:Axis,20*((z i).natAbs+1)≤n.val)
    (hd:d≤W.p.order) (hp:d≤W.p.power) (hs:∀ t,HasOrderAt (S.places t (o v)) 1 d)
    (q:Coefficient F n) (shape:q.Format (o v) Y W) (price:q.remBound (o v) W κ b)
    (signed: q.density (o v) S W =ᶠ[𝓝 1] fun U=>(W.eval U:ℂ)*(L.E.log x U).part (B.fire v)) :
    let r:=4*reg
    let s:=(factor Y S W.p.supportExponent μ*(W.p.order.factorial:ℝ))*r
    let c:=(W.p.order.factorial:ℝ)*r+s+θ v*W.p.mass (S.footprint (o v)) (μ*(s/θ v))
    F.coeffSize q.x ≤ 2*(r+s)/θ v + wrapCost F Y * wraps W.p n*(b+c/θ v) := by
  intro r s c
  obtain ⟨A,format,pay,_,raw,_,onClear⟩:=WilsonMeasuredMarkedPrimary.posted L hw divisor valid
    soft hardPaid x v Y S he
  have germ:q.density (o v) S W =ᶠ[𝓝 1] A.density (o v) S W := by
    apply signed.trans
    filter_upwards [Juniper.Caret.flat_flags n W.p.threshold W.p.threshold_pos] with U clear
    exact onClear U clear
  have ca:=compare Y S he.sound (o v) hu hd hp hs q A shape format price pay germ
  apply ca.2.trans
  exact add_le_add ((le_div_iff₀ (hw v)).mpr (by rw [mul_comm]; exact raw)) le_rfl

end YM.Integration.WilsonMeasuredRankedGerm
