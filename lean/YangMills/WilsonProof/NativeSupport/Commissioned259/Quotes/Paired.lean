import YangMills.WilsonProof.NativeSupport.Commissioned259.Quotes.Radius
import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Telescope
/-! # QScale: BB first compares mixed W poses on these genuine reflected pair readings.

 The StrongBook pre-price *alone* on mixed homes isn't a comparison to Maxwell! Want
 convergence to I of frame changes after removing leading Dial. Use `(C5)` on mixed
 books. Include all these uses on the indicated caps & homes.

 Here the hypothesis is paid uniformly on each `d` separately (with ℓ & cash maps
 at different installations; doesn't matter what argument picks the report within those
 bounds). No leading mixed-frame relations given in this price. Enough error as here,
 comparing with the actual start prediction at this point. W tower. The detector in
 `O.Read.Point` uses reflected Far field; retain it. First leg measured at the other (larger)
 home s=r T.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Quotes
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score O.Enh O.Read Comparing Pose Original Matrix
open scoped Topology ContDiff Classical BigOperators Matrix
variable {I : Type*}{L:Filter I} {G : Gauge} {d n q m e : ℕ} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (U : Final C f S) (J Y : ℝ→PhysMS.tower S) (N : WilsonPrescription G)
    (hJ : Leading U J)
    {sim : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
local notation "late" => 𝓝[>] (0:ℝ)
local notation "δ" => g0 G
local notation "FW" => Paper.point U J
local notation "τ" => Paper.meter U J N.criterion
local notation "X" => Scale.Measure.start N.scheme N.criterion

def together : Filter (ℝ×ℝ) := late ×ˢ 𝓟 (Icc 1 2)
abbrev paired_profile := forest (0:Points 1) RootG
lemma profile_space : paired_profile ∈ conf _ := ok_wall

-- arguments to C5 mixed application: q any, t' and both cash maps shared on
-- that particular installation (just one finite purpose). Decoupling t∼g from F.3.
def team (r R : ℝ) (a b : Toon G d) : ℂ := S.classMoment (spectator U none) (fun _:Fin 2=>d) (r • paired_profile)
    ![frame J (r*R) d (Level.Dial d (Real.log R) (theory a)),frame J r d (prism (theory b))]
def Mixture (d : ℕ) := ∃ (x y : ℝ×ℝ→Change G d) (p:ℕ)(t : ℝ×ℝ→ℝ),
    Tendsto (fun i=>guide G d (x i)) together (𝓝 0) ∧ Tendsto (fun i=>guide G d (y i)) together (𝓝 0) ∧
    -- need only this from equivalence
    t=O[together] (g0 G ∘ Prod.fst) ∧ ∀ a b:Toon G d,
      (fun i=>team U J i.1 i.2 a b-array (X d) paired_profile p (t i)
          ![stand (x i) (theory a),stand (y i) (prism (theory b))])=O[together] (g0 G ∘ Prod.fst)

abbrev seatPair (d : ℕ) (r : ℝ) (b:Toon G d) : Sec G d→ₗ[ℂ] ℂ := (Levy.linear₂ (FW r d 2 paired_profile)).flip (prism (theory b))
abbrev peter (d : ℕ) (r R:ℝ) := via J r (r*R) d * Level.Dial d (Real.log R)
lemma pay_team (d:ℕ) (r R : ℝ) (a b : Toon G d) : seatPair U J d r b (peter J d r R (theory a))=team U J r R a b := by
  unfold team; change FW r d 2 paired_profile _ = _; rw [Paper.use]; congr 1; ext1 i; fin_cases i
  · change frame J r d ((frame J r d).symm (frame J _ _ _))=_; rw [LinearEquiv.apply_symm_apply]; rfl
  rfl
include hJ in
lemma same_pair (a b: Toon G d) : Tendsto (fun i : ℝ=> (seatPair U J d i b) (theory a)) late (𝓝 (GramP G d b a)) := by
  let w:= Fin.append (fun _:Fin 1=>theory a) (console 1 b); let u: MaxwellSlots C (fun (_:Fin 2)=>d):= fun i=>(Free.fields C.labels d).symm (w i)
  have h : Tendsto (fun i:ℝ=>measured U none (J i) (d:=fun _=>d) u i paired_profile) late (𝓝 (WickGoal (d:=fun _=>d) u paired_profile)):= leading_at U hJ u tendsto_id tendsto_const_nhds profile_space
  have he : WickGoal (d:=fun _=>d) u paired_profile=GramP G d b a:= Original.leading_pair a b
  rw [he] at h; apply h.congr; intro i
  change FW i d 2 paired_profile w=FW i d 2 paired_profile ![theory a,prism (theory b)]; congr 1; funext i; fin_cases i <;> rfl

variable (R : Mixture U J N d)
lemma viewc {A₁:I→Change G d}(F:Tendsto (fun i=>guide G d (A₁ i)) L (𝓝 0))(p:Sec G d)(a: Toon G d) :
    Tendsto (fun i=>coord a (stand (A₁ i) p)) L (𝓝 (coord a p)) := by
  simp_rw [stood,map_add]
  have h := (continuous_component a p).continuousAt (x:=0) |>.tendsto.comp F
  simp only [Function.comp_def, LinearEquiv.symm_apply_apply,map_zero,Submodule.coe_zero,LinearMap.zero_apply] at h
  simpa only [add_zero] using! (tendsto_const_nhds (x:=coord a p)).add h
lemma within_page (π:Way G d) (x:Points n) (p:ℕ) {t'I:I→ℝ}{u:I→ Tags G d n}{w:Tags G d n}
    (ht:Tendsto t'I L (𝓝 0))(hf:∀ i j, Tendsto (fun k=>coord j (u k i)) L (𝓝 (coord j (w i)))) :
    Tendsto (fun i=> Pose.array π x p (t'I i) (u i)) L (𝓝 (Jury.fxt π x 0 w)) := by
  have he(v:Tags G d n) : Tendsto (fun i=> Pose.array π x p (t'I i) v) L (𝓝 (Jury.fxt π x 0 v)) := by
    let f (s:ℝ):= Pose.array π x p s v; have hh : Continuous f:=by simp_rw [f,Pose.array_eq,crop_apply]; fun_prop
    rw [ show Jury.fxt π x 0 v=f 0 from Eq.symm ?_ ]; apply hh.continuousAt.tendsto.comp ht
    unfold f; rw [ Pose.array_eq,crop_apply,Finset.sum_eq_single 0 ]; simp
    · intro i _ hi; rw [Complex.ofReal_zero,zero_pow hi,zero_mul]
    simp
  rw [word_sigma w (Jury.fxt π x 0)]; simp_rw [word_sigma (u _)]; refine tendsto_finsetSum _ (fun i _=>?_); exact Tendsto.smul (tendsto_finsetProd _ (fun j _=> hf j (i j))) (he (word i))
include R hJ H
lemma team_limit (a b:Toon G d): Tendsto (fun i:ℝ×ℝ=>team U J i.1 i.2 a b) together (𝓝 (GramP G d b a)) := by
  obtain ⟨x,y,p,t,hx,hy,f,h⟩:= R
  have h0 := (g0_zero sim).comp (show Tendsto Prod.fst together late from tendsto_fst)
  have hi := (h a b).trans_tendsto h0
  have Q(i:Fin 2) (j:Toon G d) : Tendsto (fun k=> coord j (![stand (x k) (theory a), stand (y k) (prism (theory b))] i)) together
      (𝓝 (coord j (![theory a,prism (theory b)] i))) := by fin_cases i; exact viewc hx ..; exact viewc hy ..
  let F:= paired_profile; have eq : (Jury.fxt (X d) F 0) ![theory a,prism (theory b)]=GramP G d b a := by
    rw [Jury.fxt,dif_pos profile_space, begins N M H]; change Wick.moment G F _=GramP G d b a
    rw [GramP,Free.bond_eval, show F=pairPoints 0 nail from lamp _ ]; congr 1; funext i; fin_cases i <;> rfl
  have h' := within_page (p:=p) (π:=X d) (x:=F) (f.trans_tendsto h0) Q
  rw [eq] at h'; exact ( ( by simpa only [zero_add] using hi.add h' : Tendsto _ together (𝓝 (GramP G d b a)) ) ).congr (fun i=>sub_add_cancel ..)

lemma leading_step : Tendsto (fun i:ℝ×ℝ=> Comparing.columns (peter J d i.1 i.2)) together (𝓝 1) := by
  let A (i:ℝ×ℝ) := Comparing.panel (seatPair U J d i.1)
  let P (i:ℝ×ℝ):= Comparing.columns (peter J d i.1 i.2)
  have h : Tendsto (fun i=> A i*P i) together (𝓝 (GramP G d)) := by
    refine tendsto_pi_nhds.mpr fun b=> tendsto_pi_nhds.mpr fun c=> ?_
    refine (team_limit U J N hJ M H R c b).congr fun i=>?_ ; rw [ ← pay_team ]; exact beats (seatPair U J d i.1 b) _
  have ha : Tendsto A together (𝓝 (GramP G d)) := tendsto_pi_nhds.mpr fun b=> tendsto_pi_nhds.mpr fun c=> (same_pair U J hJ c b).comp tendsto_fst
  have he := (Matrix.isUnit_iff_isUnit_det _).mp (positive_unit (@GramP_pos G d))
  have hv : ContinuousAt Ring.inverse (GramP G d).det := by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ he.ne_zero
  have hP := ((continuousAt_matrix_inv _ hv).tendsto.comp ha).mul h
  rw [nonsing_inv_mul _ he] at hP; apply hP.congr'
  filter_upwards [(continuous_id.matrix_det.continuousAt.tendsto.comp ha).eventually ( eventually_ne_nhds he.ne_zero )] with i hi
  change (A i)⁻¹*(A i*P i)=P i; change (A i).det ≠ 0 at hi; rw [ ←mul_assoc,nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hi),one_mul ]
end YM.FVA2.GradedFar259.Quotes
