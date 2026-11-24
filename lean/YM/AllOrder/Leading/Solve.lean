import YM.AllOrder.Leading.Profile
import YM.X.Scheme.Measure
import YM.Pert.Position.Stage

/-!
# Solving position conditions on the physical `Final`, with trace frame supply

Use the VERY SAME nested real `D` that `PositionX.T1` uses for the
independently calculated perturbative coefficients. Not merely calling a D
supplier; actual position normalization on all sufficiently fine scales,
filtering-compatible near-identity solve. Later allow mass-independent
adjustment. No assumptions about limiting rates of any possible
perturbative coefficients or using a (potentially wrong order) rate of
position conversion: here `Aligned` checks through leading correlation and
log trace only.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Leading
open Spec Function Filter Set Extraction Climb Table Ward Trace Trace.Pilot Trace.Terrace Analysis
open Trace.Over MergeProof.East Next.UVStress Maxwell Spin Next.Rank MeasureTheory PositionX
open Pert.Position
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable {F : Spec.Final C f S} {U : ℝ → FamilyFrame S} {g : ℝ → ℝ}
variable {n j d e : ℕ} {t : Fin n → ℕ}
local notation "free" => Bel C.book
local notation "Fm" => C.labels

def physicalProfile (P : Spin.change S d) (r : ℝ) (x : Points n) :=
    (S.classMoment S (fun _ : Fin n => d) (r • x)).compLinearMap (fun _ => P.toLinearMap)
lemma physical_smooth (h : S.Hierarchy) (P : Spin.change S d) (r : ℝ) (hr : 0<r)
    (v : Fin n → (free).Field d) : ContinuousOn (fun x : Points n => physicalProfile P r x v) (conf n) :=
  (smoothZoom h.smooth (fun i : Fin n => (⟨d,P (v i)⟩ : S.Tag)) hr).continuousOn

def bankAt (h : S.Hierarchy) (P : Spin.change S d) (r : ℝ) : PositionX.Bank Fm d :=
    if hr : 0<r then fun n t => {
      toFun v := t.applyTo (fun x => physicalProfile P r x v)
      map_update_add' p i v w := by
        simp_rw [Test.applyTo,MultilinearMap.map_update_add,mul_add]
        exact integral_add (t.smearing (physical_smooth h P r hr _)) (t.smearing (physical_smooth h P r hr _))
      map_update_smul' p i c v := by
        simp_rw [Test.applyTo,MultilinearMap.map_update_smul,
          show ∀ x y : ℂ, x*(c • y)= c • (x*y) from fun x y=>show x*(c*y)=_ from mul_left_comm x c y]
        exact integral_smul ..
      }
    else 0
lemma bank_eq (h : S.Hierarchy) (P : Spin.change S d) (r : ℝ) (hr : 0<r)
    (v : Fin n → (free).Field d) (t : Test n) :
    bankAt h P r n t v = t.applyTo (fun x => physicalProfile P r x v) := by
  unfold bankAt; rw [dif_pos hr]; rfl

variable (h : Aligned F g U)
include h
lemma reaches_bank (v : Pert.Position.Section C.labels d) :
    Tendsto (fun r => lookie Fm v (bankAt F.room.kernel (U r d) r)) trail (𝓝 (lookie Fm v (pureBank Fm d))) := by
  let D j := (⟨d,v.p j⟩ : (free).Tag)
  refine (aligned_tests h D v.f).congr' ((show ∀ᶠ r in trail, 0<r from self_mem_nhdsWithin).mono
      fun r hr => (bank_eq F.room.kernel (U r d) r hr v.p v.f).symm)

-- from Contacts/Layers inclusion_all (source copied with smaller dependency surface)
omit h in
lemma moment_inclusion {T : Table C.book} {P : DiffPlan S} {d a : Caps n} (hT:T.Symmetric) (hP:P.Inclusions T)
    (ha:a ≤ d) {y:Points n}(hy:y∈conf _) (v:Ribbon S a):
    S.useAt T y (hang d (fun i=>P.rise (ha i) (v i)))=S.useAt T y (hang a v):=by
  let W:=S.useAt T y; let t(c : Finset (Fin n)) i := if i∈c then hang d (fun i=>P.rise (ha i) (v i)) i else hang a v i
  suffices H:∀ c:Finset _, W (t c) = W (hang a v) from by simpa only [t,Finset.mem_univ,↓reduceIte] using H Finset.univ
  intro c; induction c using Finset.induction_on with
  | empty=>simp only [t,Finset.notMem_empty, ↓reduceIte]
  | insert i c hi ih=>
    rw [← ih,show t (insert i c) = update (t c) i ⟨d i,P.rise (ha i) (v i)⟩ from
      (by funext j; by_cases h:j=i <;> simp [h,t,hang])]
    convert P.inclusion_slot hP hT (ha i) hy i (t c) (v i) using 1; congr 1
    funext j; by_cases h:j=i <;> simp [h,t,hang,hi]
lemma nested_bank (hd : d ≤ e) : ∀ᶠ r in trail,
    pulls (PositionX.up Fm hd) (bankAt F.room.kernel (U r e) r) = bankAt F.room.kernel (U r d) r := by
  filter_upwards [h.nested d e hd, show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin] with r hr hs
  funext n t; ext1 v
  change bankAt _ (U r e) r n t (fun i => PositionX.up Fm hd (v i))=bankAt _ (U r d) r n t v
  rw [bank_eq _ _ r hs,bank_eq _ _ r hs]; apply t.apply_eq; intro x hx
  let w j := U r d (v j); let he(i : Fin n): d ≤ e:=hd
  change S.useAt S (r • x) (hang (fun _=>e) (fun i=>U r e ((Free.scheme C.labels).rise hd (v i))))=S.useAt S (r • x) (hang (fun _=>d) w)
  simp_rw [hr]
  exact moment_inclusion (a:=fun _=>d) F.room.kernel.laws.toSymmetric F.phase.transport.injection he ((enlarged hs x).1 hx) w
omit h

section adjustment
/-- Choose the near-identity branch for physical data at each scale. -/
def incrementFrame (D : Detector Fm d) (r : ℝ) (P : Spin.change S d) (h : S.Hierarchy) :=
    D.solve0 (bankAt h P r)
variable (kiosk : Bare.Shop C.labels) (hG : G.Simple)
def selectors (U : ℝ → FamilyFrame S) (hG : G.Simple) (kiosk : Bare.Shop C.labels) (h : S.Hierarchy)
    (d : ℕ) (r : ℝ) : Buffer C.labels d :=
    incrementFrame (nested C.labels hG kiosk d) r (U r d) h

include h kiosk hG
lemma zero_tail (d : ℕ) : Tendsto (fun r => selectors U hG kiosk F.room.kernel d r) trail (𝓝 0) := (PositionX.nested C.labels hG kiosk d).appears_solve0 (reaches_bank h)
lemma solves (d : ℕ) : ∀ᶠ r in trail, (PositionX.nested C.labels hG kiosk d).D (market C.labels (selectors U hG kiosk F.room.kernel d r) (bankAt F.room.kernel (U r d) r))=(PositionX.nested C.labels hG kiosk d).D (pureBank C.labels d) :=
    ((PositionX.nested C.labels hG kiosk d).patches (reaches_bank h)).mono fun _ => (PositionX.nested C.labels hG kiosk d).patch_solves
lemma compatible (hd : d ≤ e) : ∀ᶠ r in trail, selectors U hG kiosk F.room.kernel d r = zoomL C.labels hd (selectors U hG kiosk F.room.kernel e r) := by
  have ht : Tendsto (fun r => zoomL C.labels hd (selectors U hG kiosk F.room.kernel e r)) trail (𝓝 0) := by
    let W : Buffer C.labels e →L[ℝ] Buffer C.labels d := LinearMap.toContinuousLinearMap (𝕜:=ℝ) (E:=Buffer C.labels e) (F':=Buffer C.labels d) (zoomL C.labels hd)
    have hm : W 0=0 := W.map_zero
    exact hm ▸ W.continuous.continuousAt.tendsto.comp (zero_tail h kiosk hG e)
  filter_upwards [(PositionX.nested C.labels hG kiosk d).legal (reaches_bank h) ht,nested_bank h hd, solves h kiosk hG e] with r hr hN he
  refine hr.mp (?_)
  rw [← hN, ← market_proj, ← pure_zoom C.labels hd, ← zoom_compat, ← zoom_compat, he] -- orientation
omit h kiosk hG

def adjustment {L : Labels.Frames G} (b : Buffer L d) : E L d ≃ₗ[ℂ] E L d :=
    if ht : IsUnit (motor L b) then
       LinearEquiv.ofBijective (frameC L b) (ContinuousLinearMap.isUnit_iff_bijective.mp ht)
    else LinearEquiv.refl ..

def reframe (U : ℝ → FamilyFrame S) (hG : G.Simple) (kiosk : Bare.Shop C.labels) (h : S.Hierarchy)
    (r : ℝ) : FamilyFrame S :=
    fun d => (adjustment (selectors U hG kiosk h d r)).trans (U r d)
include h kiosk hG
lemma reframe_slot (d : ℕ) : ∀ᶠ r in trail, (adjustment (selectors U hG kiosk F.room.kernel d r)).toLinearMap = frameC C.labels (selectors U hG kiosk F.room.kernel d r) := by
    filter_upwards [(zero_tail h kiosk hG d).eventually (invertible_tail C.labels d)] with r hr
    unfold adjustment; rw [dif_pos hr]; rfl
lemma solve_branch (d : ℕ) : ∀ᶠ r in trail, bankAt F.room.kernel ((reframe U hG kiosk F.room.kernel) r d) r=market C.labels (selectors U hG kiosk F.room.kernel d r) (bankAt F.room.kernel (U r d) r) := by
    filter_upwards [reframe_slot h kiosk hG d, show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin] with r hr hs
    funext n t; ext1 v; change (_:ℂ)=bankAt F.room.kernel (U r d) r n t (fun i=>frameC C.labels (selectors U hG kiosk F.room.kernel d r) (v i))
    rw [bank_eq _ _ r hs,bank_eq _ _ r hs]; apply t.apply_eq; intro x hx
    rw [← hr]; rfl
lemma adjust_near (d : ℕ) : Tendsto (fun r=>Pilot.opEquiv (adjustment (selectors U hG kiosk F.room.kernel d r))) trail (𝓝 1) := by
    refine Dash.fit_plane _ LinearMap.id ?_
    intro v; have he : (fun b:Buffer C.labels d => motor C.labels b v) 0=v := add_zero v
    have hx:= (motor_diff (F:=C.labels) v).continuous.continuousAt.tendsto.comp (zero_tail h kiosk hG d)
    change motor C.labels 0 v=v at he
    rw [he] at hx; apply hx.congr'; filter_upwards [reframe_slot h kiosk hG d] with r hr
    -- infer coercion
    exact (LinearMap.congr_fun hr v).symm
omit h kiosk hG in
lemma tendsto_near_inv {L : Type*} [NormedAddCommGroup L] [NormedSpace ℂ L] [FiniteDimensional ℂ L]
   [CompleteSpace L] {ι : Type*} {l : Filter ι} {U : ι → L≃ₗ[ℂ]L} (h : Tendsto (Pilot.opEquiv ∘ U) l (𝓝 1)) :
   Tendsto (fun i=>Pilot.opEquiv (U i).symm) l (𝓝 1) := by
   have hr:=NormedRing.inverse_continuousAt (1: (L→L[ℂ] L)ˣ)
   have hh:= hr.tendsto.comp h; rw[Units.val_one,Ring.inverse_one] at hh
   apply hh.congr; intro i
   let x:=U i; let p:= Pilot.opEquiv x; let q:=Pilot.opEquiv x.symm
   have hk:p*q=1:= ContinuousLinearMap.ext (fun i=> x.apply_symm_apply _)
   have ht:q*p=1:=ContinuousLinearMap.ext (fun i=> x.symm_apply_apply _)
   have hu:IsUnit p:=⟨⟨p,q,hk,ht⟩,rfl⟩
   apply hu.mul_right_inj.mp; change _=p*q; rw [hk]; exact Ring.mul_inverse_cancel p hu
omit h kiosk hG in
lemma adjRespect {b : Buffer C.labels d} (u : Spin.change S d) (hU : Spin.realH F.room.kernel.spin (Free.spin_free C.labels) u) :
    Spin.realH F.room.kernel.spin (Free.spin_free C.labels) ((adjustment b).trans u) := by
    unfold adjustment; split_ifs with h; swap; · exact hU
    constructor
    · intro i v; change u (motor C.labels b (Pert.Rigid.wear C.labels d i v))=_
      rw [Pert.Rigid.wear_ride, ← motor_spin,← Pert.Rigid.wear_ride]; exact hU.1 ..
    intro v; change u (motor C.labels b ((freeTable C.labels).conj (Extra.FD.table_spin C.labels) d v))=_
    rw [← motor_bar]; exact hU.2 ..

set_option maxHeartbeats 200000 in
lemma in_frame : Aligned F g (reframe U hG kiosk F.room.kernel) := by
    have hp : Tendsto (fun r=>Pilot.opEquiv (adjustment (selectors U hG kiosk F.room.kernel 4 r)).symm) trail (𝓝 1):=
       tendsto_near_inv (U:=fun r => adjustment (selectors U hG kiosk F.room.kernel 4 r)) (adjust_near h kiosk hG 4)
    refine ⟨fun d => (h.respects d).mono (fun r=>adjRespect (F:=F) (U r d)),?_,?_,?_,?_,?_⟩
    · intro d; filter_upwards [reframe_slot h kiosk hG d,h.unit d] with r hr hs
      change U r d ((adjustment (selectors U hG kiosk F.room.kernel d r)).toLinearMap _)=_
      rw [hr,frameC_motor, motor_unit, hs]
    · intro d e hd; filter_upwards [compatible h kiosk hG hd,h.nested d e hd,reframe_slot h kiosk hG d,reframe_slot h kiosk hG e] with r hr ht hp he v
      change U r e ((adjustment (selectors U hG kiosk F.room.kernel e r)).toLinearMap (PositionX.up C.labels hd v)) = F.sector.derivatives.rise hd (U r d ((adjustment (selectors U hG kiosk F.room.kernel d r)).toLinearMap v))
      rw [hp,he, hr, ← frameC_up]; -- direction? RHS nested
      exact ht _
    · intro n v j kiosk' hk hV ε he
      let t i := (v i).1; let V (i:Fin n) := (v i).2; let A r i := adjustment (selectors U hG kiosk F.room.kernel (t i) r) (V i)
      have hx : ∀ i, Tendsto (fun r => A r i) trail (𝓝 (V i)):=
         fun i => Dash.arcing (adjust_near h kiosk hG (t i)) (tendsto_const_nhds (x:=V i))
      exact moving (j:=j) h (t:=t) hx kiosk' hk hV _ he
    · intro i j; apply (Dash.arcing hp (h.generator i j)).congr; intro r
      exact ((adjustment (selectors U hG kiosk F.room.kernel 4 r)).symm.toLinearMap.restrictScalars ℝ).map_smul ..
    exact Dash.arcing hp h.trace

/-- `Aligned` in the nested-D scheme with the coupling still only stated in
leading units. `U` (input) uses the Scribe diagonal; `(reframe U hG kiosk F.room.kernel)` is the actual
reparameterized field solve. Lower-grade/horizon compatibility **proved**. -/
theorem solves_position_in_frame :
    Aligned F g (reframe U hG kiosk F.room.kernel) ∧ ∀ d : ℕ, ∀ᶠ r in trail,
      (PositionX.nested C.labels hG kiosk d).D (bankAt F.room.kernel ((reframe U hG kiosk F.room.kernel) r d) r)=(PositionX.nested C.labels hG kiosk d).D (pureBank C.labels d) := by
    refine ⟨in_frame h kiosk hG,fun d=>?_⟩
    filter_upwards [solve_branch h kiosk hG d, solves h kiosk hG d] with r hr hs
    rw [hr,hs]
end adjustment
end YM.AllOrder.Leading
