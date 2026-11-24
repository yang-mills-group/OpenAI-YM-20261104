import YM.LocalTaylorR2.Mesh.Flat
import YM.LocalTaylorR2.Snapshot

/-!
 # Haar in the EXPONENTIAL Lie chart, prices on the actual hot branches
 Using still the full Ξ costs on partners; UV-independent geometry.
 Exact identity for J-curvature used here (Outer construction supplies Haar).
 The profiled expansion includes every Lie argument power up through p.
 The force sector is retained verbatim. Estimates adapted from Intrados and Drop.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Mesh
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Port Channel Next.Foundations Itinerary Glass Zest
open Work.G05
variable {Ñ:ChartRatio G} {p:ℕ} {a:ℝ} {i:Bond f}

def soloLetter (i:Bond f): LogIndex c f:= Sum.inr (.inl (.inr (.inr i)))

def curved (Ñ:ChartRatio G)(p:ℕ) (a:G.Color) := blockTaylor p (fun x=> Real.log (Ñ.J x)) a

def profile (Ñ:ChartRatio G)(p:ℕ)(X:Coat T F)(a:ℝ)(u:Directions G f)(i:Bond f):=
   if i∉X.plaza (X.seeds.dome (304*X.B)) ∧ X.Hot i then X.cone (2*a) u i * curved Ñ p (u i) else 0

def quanta (_H:Cash W s μ L Q o C T R) (p:ℕ)(i:Bond f): Port.Test T:=fun _ X w=> profile Q.table p X o.a (worldZ X R.beta w) i

lemma halo (h:LocalRatio Ñ)(v:G.El)(x:G.Color): curved Ñ p (skew v x)=curved Ñ p x:=by
  let f (x:G.Color):= Real.log (Ñ.J x)
  have he : ContDiffAt ℝ ω f 0:= (h.germ 0 (Metric.mem_ball_self h.patch)).log (by rw [h.anchored]; norm_num)
  let L : G.Color→L[ℝ] G.Color:= (skew v).toContinuousLinearEquiv.toContinuousLinearMap
  exact blockTaylor_equivariant (he.of_le (by exact le_top)) L (ContinuousLinearMap.id ℝ ℝ) (by filter_upwards [Metric.ball_mem_nhds (0:G.Color) h.patch] with x hx using congr_arg Real.log (keyship h v x hx)) x

variable (H : Cash W s μ L Q o C T R) (p i)
lemma sealH : Kept H (H.supportP (identityLog (soloLetter i))) (quanta H p i):=by
  constructor
  · intro F X X' w v ht hK Z hh hl hV
    have hT : Room P S T X.x:= ht.symm ▸ H.laws.data.room
    let A: Borough X X' Z w v ∅ ∅ R := ⟨hl,(observe _).1 hV,fun _ _=> Iff.rfl⟩
    have hy : town S X.B Q.halo i⊆ Z:= by unfold Coat.B; rw [ht]; exact hh
    have hq (a:ℕ)(h:a≤400): Cleanroom Z (a*X.B) (atEdge S i):=fun j hj=> town_circle hy j <| hj.trans (Nat.mul_le_mul_right _ (by have hh:=Q.buys; omega))
    obtain ⟨hp,hz⟩:=A.occupied hT i (hq 400 le_rfl)
    have hg:= (A.rooms hT R.beta).house hT (p:=i) (hq 25 (by omega)) R.beta
    have ht : Intake P T X.x R:= ht.symm ▸ H.laws.intake
    rw [X.oldysis ht.positive,X'.oldysis ht.positive] at hg
    unfold quanta profile cone; simp_rw [hp,hz,A.chi,A.flame,hg]
  · intro E _ F X hx hk V Y w hp hv ht
    have hr : Intake P T X.x R:= hx.symm ▸ H.laws.intake
    have hs := (compassBro hr.ready hp X hv (show ShellAccess S G X.x W X.width o.γ from (by rw [hx,hk]; exact H.laws.data.access)) R.beta).2.2 _ ht
    let z t:= worldZ (Art.drive X (V t) (Y t)) R.beta (w t)
    change Measurable fun t=> profile _ p X _ (z t) i; unfold profile; split
    · exact ((X.cone_b _ _).comp hs).mul ((blockTaylor_contDiff _ _ 0).continuous.measurable.comp ((measurable_pi_apply i).comp hs))
    exact measurable_const
  · intro F X hx hk _ z w; unfold quanta; have h: ShellAccess S G X.x W X.width o.γ:=by rw [hx,hk]; exact H.laws.data.access
    rw [Stained.flight X z (show P.Funds S T from H.laws.intake.ready) h]
    unfold profile; rw [binding]; split
    · rename_i he; rw [if_pos (show i∉X.plaza (X.seeds.dome (304*X.B)) ∧ X.Hot i from he)]; exact congr_arg _ (halo Q.table_exists (z (atEdge S i)) (worldZ X R.beta w i) (p:=p)) 
    next he=> exact (if_neg he).symm
  intro F X hx hk _ j b A E _ _ _ V x hq hz hA
  have hr : Intake P T X.x R:= hx.symm ▸ H.laws.intake; have he : Room P S T X.x:= hx.symm ▸ H.laws.data.room
  have hh:= H.laws.data.funds; rw [← hx,← hh.length_eq] at hA
  let X' (t:F.Slice G×Air f G):= X.wrapY t.1; let f' t:=worldZ (X' t) R.beta t.2
  let Z t y:= steer (X' t) b (fun i=> prune b (f' t i)) (V y)
  have hw:=mul_pos o.large he.fiery
  change Zest (fun t y=> profile Q.table p X o.a (worldZ _ _ (course _ _ _ _ _)) i) x j
  unfold profile; split
  · have he : Zest (fun t y=> Z t y i) x j:= (hq.foreshadow (Y:=Prod.fst) f' hz).1.replay (ContinuousLinearMap.proj i)
    have hu:= he.wand (tip (X:=X) (2*o.a*X.t))|>.paint (he.wand (p:=curved Q.table p) (blockTaylor_contDiff _ _ _))
    apply hu.congr; refine Eventually.of_forall (fun y t=>?_)
    rw [Silica.proceeds (X' t) _ hr.positive]
    obtain ⟨hl,hz⟩:= (fruit (X' t) hz (V y) (f' t) (show 4*o.a*X.t≤_ by change 8*o.a*X.t≤_ at hA; nlinarith only [hA,hz.warm])).grain (X' t) hw i (2*o.a) (by rw [mul_assoc]; exact mul_pos (by norm_num) hw) le_rfl
    let S' := steer (X' t) b (f' t) (V y)
    change X.cone _ S' i=X.cone _ (Z t y) i at hl
    symm
    change X.cone _ S' i * curved _ _ (S' i)= X.cone _ (Z t y) i * _
    rw [← hl]; by_cases h:X.cone (2*o.a) S' i=0
    · simp [h]
    rw [show S' i=Z t y i from hz h]
  exact Zest.still _
end YM.LocalTaylorR2.Mesh
