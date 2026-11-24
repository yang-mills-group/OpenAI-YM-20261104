import YM.Integration.WilsonOriginalPublicReflectedInterval

/-! Blocking an entire half of the trial. Its support is the union of
the actual mark windows. Marks on the same side may overlap, whereas
opposite sides use disjoint draws at every original RG step. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferCones
open Function Set Lattice RG Wilson Cells MeasureTheory
open PhysicalNext.Repeat.Legato Push.GridApprox OPE.Strobe OPE.Therm
open WilsonOriginalPublicReflectedTrace WilsonOriginalPublicReflectedGrid
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){K N p m:ℕ}
local notation "C₀" => R.family
local notation "H₀" => R.family.path
local notation "X" j:max => Config G ((C₀).side j p)
variable {ι κ:Type*}

def windows {n:Side}(o:ι→Site n)(r:ℕ):Set (Site n):=⋃i,window (o i) r

def grown (o:ι→Site ((C₀).side K p))(r:ℕ)(q:K ≤ m):Set (Site ((C₀).side m p)):=
  windows (fun i=>anchor (C₀).S p q (o i)) (grows (H₀).levels K r q)

private theorem initial (x:Site ((C₀).side K p)):anchor (C₀).S p (le_refl K) x=x:=by
  unfold anchor Ratio.embed Schedule.toDepth
  simp only [tsub_self,Schedule.steps]
  rw [show ((1:Side).val:ℕ)=1 from rfl,one_smul,wrap_lift]

theorem inside (o:ι→Site ((C₀).side K p))(r:ℕ)(q:K ≤ m){P:X K→ℂ}
    (loc:Interior (windows o r) P):Interior (grown R o r q) (backTo H₀ N p q P):=by
  induction m,q using Nat.le_induction with
  | base => simpa only [grown,grows,Nat.leRecOn_self,backTo,initial] using loc
  | succ m q ih =>
    let S:=(H₀).levels.clock.op m p
    let β:=(H₀).β N p (m+1)
    let F:=backTo H₀ N p q P
    have hf:=cylinder_env ih
    have kernel:=(H₀).levels.transition_mass m p β
    have charged:=back_env kernel hf
    rw [backTo_next]
    refine ⟨?_,charged.meas,back_local ((H₀).levels.blocks m p).branches hf ih.localSites β _ ?_,charged.cost⟩
    · intro t U
      have move:=back_natural kernel hf (gauge t) (gauge (t ∘ S.ratio.embed))
        (prior_gauge _) (fun a b=>((H₀).levels.blocks m p).gauge β a b t)
      rw [show F ∘ gauge (t ∘ S.ratio.embed)=F from funext (ih.gauge _)] at move
      exact (congr_fun move U).symm
    · intro x hx y hy
      obtain ⟨i,atx⟩:=mem_iUnion.mp hx
      apply mem_iUnion.mpr;refine ⟨i,?_⟩
      dsimp only
      rw [grows_next,←anchor_next]
      · exact window_add (window_embed _ atx) hy
      all_goals exact q

theorem factors (o:ι→Site ((C₀).side K p))(a:κ→Site ((C₀).side K p))(r:ℕ)(q:K ≤ m){P Q:X K→ℂ}
    (left:Interior (windows o r) P)(right:Interior (windows a r) Q)
    (apart:∀i j,2*muzzle (H₀).levels K r<separation (o i) (a j)):
    backTo H₀ N p q (P*Q)=backTo H₀ N p q P*backTo H₀ N p q Q:=by
  induction m,q using Nat.le_induction with
  | base => simp only [backTo, Nat.leRecOn_self]
  | succ m q ih =>
    rw [backTo_next H₀ N p q,ih,backTo_next H₀ N p q,backTo_next H₀ N p q]
    have hl:=inside (N:=N) R o r q left
    have hr:=inside (N:=N) R a r q right
    apply back_factors ((H₀).levels.blocks m p).branches (cylinder_env hl) (cylinder_env hr) hl.localSites hr.localSites
    apply Set.disjoint_left.mpr
    intro z hz hq
    obtain ⟨i,zi⟩:=mem_iUnion.mp hz
    obtain ⟨j,zj⟩:=mem_iUnion.mp hq
    exact Set.disjoint_left.mp (freedom (A:=H₀) (o i) (a j) (apart i j) q) zi zj

theorem returned (q:K≤N)(cut:Cut ((C₀).side N p))(seam:Site ((C₀).side K p))
    (fit:anchor (C₀).S p q seam=cut.slide)(o:ι→Site ((C₀).side K p))(a:κ→Site ((C₀).side K p))
    (r:ℕ){P Q:X K→ℂ}(left:Interior (windows o r) P)(right:Interior (windows a r) Q)
    (apart:∀i j,2*muzzle (H₀).levels K r<separation (o i) (affine cut.flip seam (a j))):
    pairing R K N p cut.flip seam P Q=Cells.form ((C₀).beta N p) cut (backTo H₀ N p q P) (backTo H₀ N p q Q):=by
  let T:=Q ∘ pull cut.flip seam
  have reflected:Interior (windows (fun j=>affine cut.flip seam (a j)) r) T:=by
    apply right.unchanged cut.flip seam
    intro x hx
    obtain ⟨i,xi⟩:=mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i,window_affine _ _ _ xi⟩
  have paired:=factors (N:=N) R o (fun j=>affine cut.flip seam (a j)) r q left reflected.real apart
  have turns:=backTo_orient H₀ N p (le_refl K) q seam cut.flip (cylinder_env right)
  rw [initial,fit] at turns
  have conj:=backTo_star H₀ N p q (cylinder_env reflected)
  have heard:=OPE.Therm.retro R.makes.wilson q le_rfl (P*(fun U=>star (T U))) ((cylinder_env left).mulC (cylinder_env reflected.real))
  refine heard.symm.trans ?_
  change (∫U,backTo H₀ N p q (P*(fun U=>star (T U))) U ∂scene H₀ N p N)=_
  rw [WilsonPositionOriginalDiagnosticReflected.same R N p,paired,conj]
  change Wilson.moment _ (fun U=>_ * star (backTo H₀ N p q T U))=_
  rw [show backTo H₀ N p q T=_ from turns]
  rfl

end YM.Integration.WilsonMeasuredPublicEntranceTransferCones
end
