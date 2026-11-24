import YM.MS.Orbit.Clove
/-!
# The continuum-torus root filter identity for image tadpoles. Read form once. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Function Filter Set Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City
open scoped Topology ContDiff Interval
variable {I E:Type}{G: Gauge}{n:Side}{F H:QP→I}{A:QP→ℂ}{p q:QP}{b:Cover}
abbrev pinQ {E:Type}(F:QP→E): Prop:= ∀ {p q}, congrQ p q→ F p=F q
lemma pin_C (hu: pinQ F): ∀ c:Cover,Periodic F (rep c):=fun c _=> hu ⟨ c,rfl ⟩
lemma pinP (h: ∀ c:Cover,Periodic F (rep c)): pinQ F:= by rintro _ _ ⟨a,rfl⟩; exact h a _
abbrev decap (p:QP):= ( (2:ℝ)⁻¹ ) • p
abbrev root_q (p:QP)(i:Half):= -(decap p)+ Coord i
def Hβ (f:QP→ℂ)(p:QP):= ∑ i:Half,f (root_q p i)
lemma skip (p q:QP): decap (p+q)=decap p+decap q := smul_add ..
lemma orderP (z:Cover): decap (rep z)= walk Kappa z := rfl
lemma branchM (p:QP) (z:Cover) (x:Half): congrQ (root_q (p+rep z) (wrap Kappa z+x)) (root_q p x):= by
    unfold root_q; rw [skip,orderP]; apply congrQ.trans ( (congrQ.normal _).plus (congrQ.sym (ξ_add ..) ) ); obtain ht:= congrQ.sym (ξ_rel ( n:=Kappa ) z); refine congrQ.trans ((congrQ.normal _) |>.plus ( ht.plus (congrQ.normal _) )) ?_; rw [show -(_+ walk Kappa z) + ( walk Kappa z+Coord x)= -(decap p)+Coord x from (by abel)]; exact congrQ.normal _ -- abel argument
lemma pin_root (h:pinQ A): pinQ ( Hβ A ):= pinP fun b x=> by unfold Hβ; rw [ ← Equiv.sum_comp (Equiv.addLeft ( wrap Kappa b )) (fun i:Half=>A (root_q (x+rep b) i)) ]; exact Finset.sum_congr rfl fun i _=> h (branchM ..)
-- when p in range actual.$Z^- = −wrap lift parent
abbrev min_v (p:Zone n) := wrap (periodN n) (- Lattice.lift ( (α_frame n).parent p ))
lemma climb (p:Zone n): thumb n ( min_v p )= -(α_frame n).parent p:= by rw [ min_v, show thumb n (wrap (periodN n) _)=_ from (τ_frame n).residue_wrap _, map_neg,wrap_lift ]
lemma decR (p:Zone n)(h:ParSec n p=0) : decap (Coord p)= walk (periodN n) ( Lattice.lift ( (α_frame n).parent p )) := by
    unfold Coord wrapZ; nth_rw 1 [ Liftβ n p h ]; rw [ Subs,Ratio.root_embed, (α_frame n).lift_embed ]; -- congr.Subs→embed
    let v:= (α_frame n).parent p; change decap ( walk _ ( (2:ℕ) • Lattice.lift v ) )=_; rw [ map_nsmul, two_smul ]; unfold decap; rw [← two_smul ℝ, smul_smul, inv_mul_cancel₀ (by norm_num : (2:ℝ)≠0), one_smul ] -- two_smul ℝ
lemma climbβ (p:Zone n)(h:ParSec n p=0)(j:Half): congrQ ( Coord (min_v p+thin n j)) (root_q (Coord p) j) := by
    apply congrQ.trans ( congrQ.sym (ξ_add ..) ); rw [ make_coord ]; unfold root_q; rw [decR p h,← map_neg]; exact ( congrQ.sym (ξ_rel (n:=periodN n) _))|>.plus (congrQ.normal _ )
lemma Q_read (p:Zone n)(q:QP)(h:congrQ q (Coord p))(hp:pinQ A): (∑ i:Zone n, if i+i+p=0 then A (Coord i) else 0) = if ParSec n p=0 then Hβ A q else 0 := by
    split_ifs with he; · simp_rw [enter p _ he, ← climb p, window_roots, pin_root hp h, Hβ ]; exact Finset.sum_congr rfl fun i _=> hp (climbβ p he i)
    exact Finset.sum_eq_zero fun _ _=> if_neg (fun h=> he (curtain h))
lemma junction (p:Zone n)(q:QP)(h:congrQ q (Coord p))(hp:pinQ A): (∑ i:Zone n, if i+i+p=0 then A (Coord i) else 0) = ∑ i:Half, Bloch.cell (thin n i) p * ((1/16:ℂ) * Hβ A q):= by
    rw [ ← Finset.sum_mul,check_total,Q_read p q h hp ]; split_ifs <;> ring
end YM.MS.Orbit
