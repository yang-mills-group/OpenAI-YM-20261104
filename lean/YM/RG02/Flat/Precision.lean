import YM.RG02.Flat.Sworn
import YM.RG02.Flat.Branch
import YM.AnalyticNext.QUARTIC_MATCH.Scene
import YM.RG02.Limit.Steering

/-!
`Γ`: covariance always defined from the vacuum *fine Haar slice* (full
finite torus) and full unmasked incoming PathData and actual normalized branch
score. The pinned coordinatization uses RELATIVE fine links:
 reparametrizing the coarse representative still multiplies replica on RIGHT.
The mean with this convention must be the same PS `Guessed`; on-shell value
agrees with the slope of the coarse action. The tag (predictor) slot is
used while forming the Gaussian: on this flat branch no redraw changes it.
Near the stationarity germ only. Charges pointwise; support reinterpretation
and covariance kernel bounds are NOT assertions on this metric space!
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Tangent
open Filter Function Set Matrix Lattice Wilson RG Precision Exterior Tree Supply Bid
open PertExtension PertExtension.GaussianScore PertExtension.Series AnalyticNext.QuarticMatch
open scoped Topology Classical ContDiff BigOperators Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {c f : Side}{S : StepData c f}

variable (T : Forest S.ratio)

/-- Primitive pre-reset parameter directions. -/
def shift (x : Dir G c) : ℝ × AxisChart G T →L[ℝ] Dir G c × AxisChart G T :=
   ((ContinuousLinearMap.toSpanSingleton ℝ x) ∘L ContinuousLinearMap.fst _ _ _).prod
     (ContinuousLinearMap.snd ℝ ℝ _)

def ray (t : S.Choices)(p : Clip)(R : PathData G)(B : Dir G c) := uncurry (tested T t p R) ∘ (shift T B)
def crest (ρ : Dir G c → AxisChart G T)(B : Dir G c) := fderiv ℝ ρ 0 B

def edge (t : S.Choices)(p : Clip)(R : PathData G) := Work.F05.bend (tested T t p R 0) 0

def due (t : S.Choices)(p : Clip)(R : PathData G)(B : Dir G c)(u : AxisChart G T) := Radial.jet (ray T t p R B) 2 (1,u)
variable {T} (t : S.Choices) {p : Clip}{R : PathData G}{ρ : Dir G c → AxisChart G T} {w : ℝ} (hw : w > 0)

section law
private lemma standard {X : Type}[NormedAddCommGroup X][NormedSpace ℝ X] (f : X→ℝ)(x:X) :
   Radial.jet f 2 x=Work.F05.bend f 0 x x / 2 := by
   unfold Radial.jet; rw [show (fun _ : Fin 2 => x)= ![x,x] from funext fun i=>by fin_cases i <;> rfl, Work.F05.bend_apply]
   norm_num; ring
variable (hh : PriceGap T p R w)(ht : Critical T p R ρ)
include hw hh
lemma score_gap : ∃ c>0,∀ x : AxisChart G T,c*‖x‖^2 ≤ edge T t p R x x/2 := by
   have H : ∀ x:AxisChart G T,x ≠ 0 → 0 < Radial.jet (tested T t p R 0) 2 x := by
      intro x hx; rw [standard]; exact div_pos (Work.F05.tested_diag hw hh t x hx) (by norm_num)
   obtain ⟨c,hc,H⟩ := Radial.quadratic_min (f:=tested T t p R 0) H
   · exact ⟨c,hc,fun x=> (H x).trans_eq (standard ..)⟩

include ht
/-- Use with `Orientation.certifies` or the actual `Kin`. -/
def Γ : Law (AxisChart G T) where
    P := edge T t p R
    slope := score_gap t hw hh
    smooth := by
       have he (x:AxisChart G T) : edge T t p R x x=Radial.jet (tested T t p R 0) 2 x * 2 := by rw [standard, div_mul_cancel₀ _ (by norm_num)]; rfl
       simp_rw [he]; exact (Radial.Smooth.continuousJet _ _).mul continuous_const
    turns x y := by
       have hs : ContDiffAt ℝ ω (tested T t p R 0) 0 := by
         exact ((ht.2.2 t).1).comp (f:=fun i => ((0:Dir G c),i)) 0 (contDiffAt_const.prodMk contDiffAt_id)
       simp only [edge, Work.F05.bend_apply, iteratedFDeriv_two_apply]; exact hs.isSymmSndFDerivAt_of_omega ..

lemma precision_agrees (B : Bed)(h : Comptroller T B p R)(x y : AxisChart G T) :
    (Γ t hw hh ht).P x y = gaugeFiscal B (Bid.stretch (S:=S) T (0,x)) (Bid.stretch (S:=S) T (0,y)) +
      S.kernel.penalty * ∑ i : Body 1 c, inner ℝ (Bid.crop T ((0:Dir G c),x) i) (Bid.crop T (0,y) i) := by
   let F := uncurry (tested T t p R); let X := ContinuousLinearMap.inr ℝ (Dir G c) (AxisChart G T)
   change edge T t p R x y= _
   rw [edge]; change Work.F05.bend (F ∘ X) 0 x y= _
   have hu := Work.F05.bend_comp_stationary (x:=0) (g:=(X : AxisChart G T → _)) (by rw [X.map_zero]; exact (ht.2.2 t).1) X.contDiff.contDiffAt (by rw [X.map_zero]; exact (h t).2.1)
   rw [hu, X.fderiv]; simp only [X.map_zero]
   change Work.F05.bend F 0 _ _ = _
   rw [Work.F05.bend_apply]
   exact (h t).2.2 _ _

omit hw hh ht in
private lemma pearl {V : Type}[NormedAddCommGroup V][NormedSpace ℝ V] {P Q : Law V} (h:P.P=Q.P) : P=Q := by
   cases P; cases Q; dsimp only at h; subst_eqs; rfl

lemma tag_constant (h : S.patch.Branches S.kernel G)(u : S.Choices) : Γ u hw hh ht=Γ t hw hh ht := by
   apply pearl
   have he := Work.F04.tested_germ h T p R u t
   exact Work.F05.bend_congr (Work.F05.hold_near he)

lemma launch {B : Bed}(h : Comptroller T B p R)(x : Dir G c) :
   Therm.Steer (Γ t hw hh ht) (ray T t p R x) (due T t p R x (crest T ρ x)) (crest T ρ x) := by
   let Y := shift T x; let F := uncurry (tested T t p R)
   have hf : ContDiffAt ℝ ω F 0 := (ht.2.2 t).1
   have hb : Radial.Stationary (F ∘ Y) := {
      smooth := ((show ContDiffAt ℝ ω F (Y 0) by rw [map_zero]; exact hf).comp 0 (Y.contDiff.contDiffAt)).of_le le_top
      base0 := (congr_arg (fun u => F u) Y.map_zero).trans (h t).1
      base1 u := by
         rw [Radial.jet,iteratedFDeriv_one_apply, fderiv_comp 0, map_zero, show fderiv ℝ F 0=0 from (h t).2.1]; simp
         · rw [map_zero]; exact hf.differentiableAt (by simp)
         exact Y.differentiableAt }
   refine ⟨hb, fun s y=> ?_⟩
   let u := crest T ρ x
   have hs := SliceExchange.on_shell t ht
   have hc : arc ρ 0=0 := Prod.ext rfl ht.1
   let D := Work.F05.bend F 0
   have hv y : D (x,u) ((0:Dir G c),y)=0 := by
       change Work.F05.bend F 0 _ _ = _
       rw [Work.F05.bend_apply,D2_jet,← hc]
       exact hs.flat x y
   have hU y : D ((0:Dir G c),y) (x,u)=0 :=
       (show D _ (x,u)=D (x,u) _ from (hf.isSymmSndFDerivAt_of_omega ..)).trans (hv y)
   have hp (v : ℝ × AxisChart G T) : Radial.jet (F ∘ Y) 2 v=D (Y v) (Y v)/2 := by
      rw [standard, Work.F05.bend_comp_stationary, Y.fderiv, map_zero];
      · rfl
      · rw [Y.map_zero]; exact hf
      · exact Y.contDiff.contDiffAt
      rw [Y.map_zero]; exact (h t).2.1
   let X := ContinuousLinearMap.inr ℝ (Dir G c) (AxisChart G T)
   have hq (v w) : (Γ t hw hh ht).P v w = D ((0:Dir G c),v) ((0:Dir G c),w) := by
      change Work.F05.bend (F ∘ X) 0 _ _= D _ _
      rw [Work.F05.bend_comp_stationary, X.fderiv, map_zero]
      · rfl
      · rw [map_zero]; exact hf
      · exact X.contDiff.contDiffAt
      rw [map_zero]; exact (h t).2.1
   change Radial.jet (F ∘ Y) 2 (s,y) = s^2*Radial.jet (F ∘ Y) 2 (1,u)+(Γ t hw hh ht).P (y-s • u) (y-s • u)/2
   rw [hp,hp,show Y (s,y)=s • (x,u)+ (0,y-s • u) from Prod.ext (add_zero ..).symm (add_sub_cancel ..).symm,
       show Y (1,u)=(x,u) from Prod.ext (one_smul ℝ x) rfl]
   simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply]
   simp only [hv,hU,smul_eq_mul,hq]
   ring
end law

-- tangential coordinate check + coarse slope. Name matrix W same period only.
lemma priced {K : Precision.MapPrices}{O : ChartRatio G}{s : Supply.Sheet G}{p₁ : Supply.Rolls s}{Q : Precision.PostCost p₁}
    {a : Levels G}{M : Horizon a}{R : Kin M O}(hk : M.Suffices K)(hr : R.Planned Q)
    {N m : ℕ}(z : m<N)(P : ℕ)(T : Forest (a.clock.op m P).ratio) (t : (a.clock.op m P).Choices)(x : Dir G (a.S.side m P)) :
    let U := crest T (R.stationary N m P T) x
    U=relative T (Bloch.installed (a.clock.op m P).ratio (M.towers N m).A0) x ∧
    due T t (a.params (m+1)).clip (R.path N (m+1)) x U= gaugeFiscal (M.H N m) x x /2 := by
   intro u
   obtain ⟨hv,hG⟩ := hr.critical N m P z T
   have hb := Orientation.certifies hk hr P z T
   have hh : u=relative T (Bloch.installed (a.clock.op m P).ratio (M.towers N m).A0) x :=
       (Push.side (R.stationary N m P T) (hv.2.1.differentiableAt (by simp)) x).unique (hG x)
   refine ⟨hh,?_⟩
   let Y := shift T x
   let W := tested T t (a.params (m+1)).clip (R.path N (m+1))
   change Radial.jet (Function.uncurry W ∘ Y) 2 (1,u)= _
   rw [standard, Work.F05.bend_comp_stationary, Y.fderiv,Y.map_zero]
   · let v : Dir G _ × AxisChart G T:=(x,u)
     change Work.F05.bend _ 0 (Y (1,u)) (Y (1,u)) /2= _; rw [Work.F05.bend_apply,show Y (1,u)=v from Prod.ext (one_smul ℝ x) rfl]
     unfold v; rw [hh]; congr 1
     exact Work.F04.test_pair T _ _ _ _ _ ((hk.crossings N m P z).trial) hb ((x,_)) x t
   · rw [map_zero]; exact (hv.2.2 t).1
   · exact Y.contDiff.contDiffAt
   rw [map_zero]; exact (hb t).2.1

end YM.RG02.Tangent
