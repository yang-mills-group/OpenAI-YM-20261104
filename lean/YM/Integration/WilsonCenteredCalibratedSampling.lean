import YM.Integration.WilsonCenteredMeasuredJunction
import YM.RG17.Gathers

/-! The cutoff-dependent raw reporter and every spectator are evaluated against
the same Wilson measure. Keep each child at its own microscopic rounded site. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCalibratedSampling
open Function Set Filter Metric MeasureTheory Analysis Table Spec Lattice Extraction Next.UVStress
open Wilson RG Source PhysicalNext.Repeat.Legato StressFlux.Matching Finset Cells
open WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking WilsonCenteredWatchedShape WilsonCenteredWatchedCylinder
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {n:ℕ} {f:Extraction.Order} {S:Table R.family.book}

private theorem cast_token {d e:ℕ}(eq:d=e)(v:R.family.label e) :
    (⟨d,eq.symm ▸ v⟩:R.family.book.Token)=⟨e,v⟩ :=by subst d;rfl

private theorem joined (d:Fin n→ℕ) (w:∀j,R.family.label (d j)) (W:Watch R.family):
    (fun k=>(⟨_,RG17.joinRef R.family d (e:=fun i=>(W.q i).1) w (fun i=>(W.q i).2) k⟩:
      R.family.book.Token))=tags R d w W :=by
  funext k
  cases k using Fin.addCases with
  | left j =>
    simp only [RG17.joinRef,Fin.addCases_left,tags,Fin.append_left]
    exact cast_token R (Fin.append_left ..) (w j)
  | right j =>
    simp only [RG17.joinRef,Fin.addCases_right,tags,Fin.append_right]
    exact cast_token R (Fin.append_right d (fun i:Fin W.n=>(W.q i).1) j) (W.q j).2

private theorem move_cast {d e:ℕ}(eq:d=e){l:Filter (ℕ×ℕ)}{w:ℕ×ℕ→R.family.label e}
    {v:R.family.label e}(h:Tendsto w l (𝓝 v)):
    Tendsto (fun k=>(eq.symm ▸ w k:R.family.label d)) l (𝓝 (eq.symm ▸ v:R.family.label d)) :=by
  subst d;exact h

private theorem restrict_test (φ:Test n)(V:Points n→ℂ):
    (∫x in tsupport (φ:Points n→ℂ),φ x*V x)=φ.applyTo V :=by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have z:φ x=0:=by by_contra ne;exact hx (subset_closure ne)
  rw [z,zero_mul]

omit R in
private theorem mesh (m:ℕ):∀ᶠ k:ℕ×ℕ in f.fuse,m≤k.1:=by
  rw [Extraction.Order.fused,Extraction.Order.late]
  exact Eventually.of_forall fun _=>f.mesh.cofinal.eventually_ge_atTop m

theorem original (F:Spec.Final R.family f S) (simple:G.Simple) (L:RG17.Layout F)
    {l:Filter (ℕ×ℕ)}[l.NeBot](lens:l≤L.lens)(d:Fin n→ℕ)(w:∀j,R.family.label (d j))
    (r:ℝ)(φ:Test n)(W:Watch R.family)(age:∀i,R.family.ref (d i)≤L.level r)
    (clear:∀x∈tsupport (φ:Points n→ℂ),joint W r x∈conf _)
    (tie:∀ᵐ x ∂volume.restrict (tsupport (φ:Points n→ℂ)),joint W r x∈generic _) :
    Tendsto (fun k:ℕ×ℕ=>moment (R.family.beta k.1 k.2) (fun U=>
      cylinder R d k (fun j=>RG17.atRef L (d j) r k (w j)) (mass R φ r k) U*W.plot k.1 k.2 U)) l
      (𝓝 (WilsonCenteredWatchedLimit.reading (S:=S) R d
        (fun j=>RG17.locatedRef L (d j) r (w j)) φ W r)) :=by
  let a (k:ℕ×ℕ)(i:Fin n):=RG17.atRef L (d i) r k (w i)
  let b (i:Fin n):=RG17.locatedRef L (d i) r (w i)
  let join := fun (t:∀i,R.family.label (d i))=>RG17.joinRef R.family d
    (e:=fun i=>(W.q i).1) t (fun j=>(W.q j).2)
  have coords (i:Fin (n+W.n)):Tendsto (fun k=>join (a k) i) l (𝓝 (join b i)):=by
    cases i using Fin.addCases with
    | left j =>
      simp only [join,RG17.joinRef,Fin.addCases_left]
      exact move_cast R (Fin.append_left ..) (RG17.tendsRef L lens tendsto_const_nhds (age j))
    | right j =>
      simp only [join,RG17.joinRef,Fin.addCases_right]
      exact tendsto_const_nhds
  let K := tsupport (φ:Points n→ℂ)
  have passage:= WilsonCenteredMeasuredJunction.original F (lens.trans L.certified)
    (μ:=volume.restrict K) (joint W r) (φ:Points n→ℂ) (join b) (fun k=>join (a k))
    (R.again simple).1.control (continuous_joint W r) φ.hasCompactSupport clear
    (ae_restrict_mem φ.hasCompactSupport.measurableSet) tie
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).restrict coords
  have read (T:Table R.family.book)(t:∀j,R.family.label (d j)) :
      (∫x in K,φ x*T.value _ (joint W r x) (join t)) =
      φ.applyTo (fun x=>T.read (joint W r x) (tags R d t W)) :=by
    rw [←joined R d t W]
    exact restrict_test φ _
  rw [read S b] at passage
  refine passage.congr' ?_
  filter_upwards [(mesh (f:=f) W.t).filter_mono (lens.trans L.certified)] with k late
  exact (read (rounded R.family k.1 k.2) (a k)).trans
    (WilsonCenteredWatchedCylinder.original R d (a k) W φ r late).symm

end YM.Integration.WilsonCenteredCalibratedSampling
