import YM.Integration.WilsonCenteredSourceScale
import YM.Integration.WilsonCloseCaptureDate
import YM.Next.RANK.Coordinates

/-! An original compact source can use a fixed multiple of its radius for
capture. Its charged microscopic cells then have their actual ancestor at the
literal origin. The change of variables preserves every signed cell mass. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredEnrolledOrigin
open Function Set Filter MeasureTheory Analysis Table Spec Lattice Extraction Next.UVStress
open Wilson RG Source PhysicalNext.Repeat.Legato StressFlux.Matching Finset Cells
open WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {n:ℕ}

private theorem central (S:Schedule) {N p j:ℕ} (live:j≤N) (x:Points n) (u:Fin n)
    (space:∀a,2*(|x u a|+S.a N)<S.a j):
    (S.toDepth live p).parent (wrap (S.side N p) (address (S.a N) x u))=0 :=by
  let g:=S.toDepth live p
  let z:=address (S.a N) x u
  have fine:=S.a_pos N
  have scaled:=S.embeds_scale g
  have component (a:Axis):2*(z a).natAbs<g.count.val:=by
    have hit:=(Extraction.tile_bounds fine (x u a) (z a)).mp rfl
    change S.a N*((z a:ℝ)-1)<x u a ∧ x u a ≤ S.a N*(z a:ℝ) at hit
    have price:|S.a N*(z a:ℝ)|≤|x u a|+S.a N:=by
      rw [abs_le]
      exact ⟨by linarith [neg_abs_le (x u a),hit.2],by linarith [le_abs_self (x u a),hit.1]⟩
    have exact_abs:S.a N*((z a).natAbs:ℝ)=|S.a N*(z a:ℝ)|:=by
      rw [abs_mul,abs_of_pos fine]
      congr 1
      rw [←show (((↑(z a).natAbs:ℤ):ℝ))=_ from Int.cast_natCast _,Int.natCast_natAbs,Int.cast_abs]
    have strict:S.a N*(2*((z a).natAbs:ℝ))<S.a N*(g.count.val:ℝ):=by
      rw [scaled]
      linarith [price,space a,exact_abs]
    exact_mod_cast (mul_lt_mul_iff_right₀ fine).mp strict
  apply Next.Rank.Station.owner g
  rw [show g.embed (0:Site (S.side j p))=0 from g.root.map_zero,separation,sub_zero]
  have bound: (univ.sup (fun a=>((lift (wrap (S.side N p) z)) a).natAbs)) ≤ (g.count.val-1)/2:=by
    apply Finset.sup_le
    intro a _
    apply (Corona.lap z a).trans
    have:=component a
    omega
  have pos:1≤g.count.val:=g.count.property
  change 2*univ.sup (fun a=>((lift (wrap (S.side N p) z)) a).natAbs)<g.count.val
  omega

theorem original (φ:Test n):
    ∃c:ℝ,∃hc:0<c,∀r:ℝ,0<r → c*r ≤ R.family.S.a 0 →
    let b:=WilsonCloseCaptureDate.level R.family.S (c*r)
    ∀(N p:ℕ)(live:b≤N),8*R.family.S.a N<R.family.S.a b →
    ∀z:Sites R (N,p) n,mass R φ r (N,p) z≠0 →
      mass R (dilate (inv_pos.mpr hc) φ) (c*r) (N,p) z=mass R φ r (N,p) z ∧
      ∀i,(R.family.S.toDepth live p).parent (z i)=0 :=by
  obtain ⟨M,diameter⟩:=φ.hasCompactSupport.exists_bound_of_continuousOn
    (continuous_id (X:=Points n)).continuousOn
  let c:=16*(|M|+1)
  have hc:0<c:=by dsimp [c];positivity
  refine ⟨c,hc,?_⟩
  intro r hr small b N p live fine z paid
  refine ⟨WilsonCenteredSourceScale.mass_at R φ hc r _ z,?_⟩
  obtain ⟨x,hx,actual⟩:=WilsonCenteredSourceScale.active R φ r _ z paid
  rw [←actual]
  have shelf: c*r ≤ R.family.S.a b:=(WilsonCloseCaptureDate.bracket _ (mul_pos hc hr) small).2
  intro i
  apply central R.family.S live (r•x) i
  intro a
  have coord:|x i a|≤M:=(show |x i a| ≤ ‖x i‖ by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (x i) a).trans
    ((PiLp.norm_apply_le x i).trans (diameter x hx))
  have shrunk:|(r•x) i a|=r*|x i a|:=by
    change |r*x i a|=_
    rw [abs_mul,abs_of_pos hr]
  rw [shrunk]
  change 16*(|M|+1)*r ≤ _ at shelf
  nlinarith [mul_le_mul_of_nonneg_left (coord.trans (le_abs_self M)) hr.le,
    mul_nonneg hr.le (abs_nonneg M)]

end YM.Integration.WilsonCenteredEnrolledOrigin
