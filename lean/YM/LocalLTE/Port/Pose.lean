import YM.LocalLTE.Port.Page
/-! # Unit installation and forecast geometry. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus FrameBox Cabana Push
open Progress.DirectedRecipe MergeProof Menu Marker Accent Overlay Fan
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge}{c f : Side}{Q : Rep G f} {S:StepData c f} {σ κ Λ μ' w t v : ℝ}
variable {V I J : Type}[DecidableEq V][Fintype V] {R:Marker.Census V}(B A C:Bands R Q)(r:V→ℝ) (hr:∀ i,0<r i) (o:V→Site f)
open Extra.Trajectories Next.Foundations
variable {d U:ℕ} {a b Y η D X E θ ρ:ℝ}
local notation "P"=> Q.p
local notation "ν"=> Q.p.threshold
local notation "W₀"=> Config G f
-- B forecast, A exact, C rem. Unit transmission general.
abbrev pairUnit (B:Marker.Census V)(u:V→ℂ):= ∑ i,Poly.send (B.fire i) (u i)
def augment (B:Bands R Q)(u:V→ℂ):Overlay.Bands R Q:= {B with units:= u}
omit [Fintype V] in
lemma tact (h:B.Active)(k:V→ℂ): (augment B k).Active:=⟨h.proper,h.pins,h.regular,h.occurs,h.retained,h.inspects,h.keeps,h.meas,h.invi⟩
omit [Fintype V] in
lemma touch (u:V→ℂ)(h:B.Radial r a b η θ)(he:∀ i,r i* ‖u i‖ ≤v): (augment B u).Radial r v b η θ:=⟨h.pure,he,h.factor,h.bulk,h.hits⟩
lemma admitsX (u:V→ℂ)(h:B.Active)(ht:B.Radial r a b η θ)(hg:B.units=0)(V:Config G f): (augment B u|>.density V)=Poly.pass (pairUnit R u)*B.density V:=by
    have hp:(pairUnit R u).part R.quiet=0:=by unfold pairUnit; rw [Poly.part_sum]; exact sum_eq_zero fun i _=> by rw [Poly.part_send,if_neg (R.fire_hot _).symm]
    let X:=∑' i,B.ray i V; have hx : X.part R.quiet=0:=by
       unfold X; rw [Poly.share (B.bulkBound h ht V|>.1)]; exact (tsum_congr fun i=> (show (B.ray i V).part R.quiet=0 from (by unfold Bands.ray; rw [Poly.part_send,if_neg (fun he=> (h.proper _).ne_empty (show (B.rays i).val=∅ from (congr_arg Subtype.val he.symm)))]))).trans tsum_zero
    have hS:B.extra V=X:=by unfold Bands.extra; rw [hg]; simp only [Pi.zero_apply, Poly.send_zero,sum_const_zero,zero_add]; rfl
    have ht:(augment B u|>.extra V)=(pairUnit R u)+X:=by change _+_= _+_; rfl
    unfold Bands.density; rw [hS,ht,Extra.Trajectories.pass_add hp hx,mul_assoc,mul_smul_comm];rfl -- possible
lemma augmentsE {w' v':ℝ} [Fintype I](q:I→ Leaf Q)(r:I→ℝ)(z:I→Poly R){K: Rep G c}(E: Bands R K)(w:V→ℝ)(u:V→ℂ)(h:E.Active)(he:E.Radial w a b t v)(hZ:E.units=0) (h0:S.IsKernel Q.beta G)(hQ: Q.Lawful σ Λ μ' w' v')
    (hp:∀ U,A.density U=Poly.pass (pairUnit R u)* Merge.Photo.given (S:=S) q r R z U)(hT:∀ U,E.density U=S.push Q.beta (Merge.Photo.given (S:=S) q r R z) U)(U:Config G c): S.push Q.beta A.density U=(augment E u|>.density U):=by
    rw [admitsX E w u h he hZ U,hT U]; let G':=Merge.Photo.given (S:=S) q r R z; let p:=Poly.pass (pairUnit R u)
    let L:Poly R→ₗ[ℂ] Poly R:= {
       toFun:=fun x=> p*x
       map_add':=fun x y=>mul_add ..
       map_smul':=fun x y=>mul_smul_comm .. }
    let F:Poly R→L[ℝ] Poly R:= L.toContinuousLinearMap.restrictScalars ℝ
    have hh: Integrable G' (prior G f):=by
       unfold G' Merge.Photo.given; refine integrable_finsetSum _ (fun i _=> ?_); let a:=(Merge.Palette.team q (S:=S) i); exact (Complex.ofRealCLM.integrable_comp ((a.sells hQ|>.1.integrable _).mul_const _)).smul_const _ -- edit synt
    have hv:= F.integral_comp_comm (StepData.push_slice h0 U G' hh); simp_rw [F.map_smul] at hv; unfold StepData.push; simp_rw [hp]; exact hv
end YM.LocalLTE.Port
