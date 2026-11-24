import YM.LocalLTE.Port.Moment
import YM.LocalLTE.Quartz.Core
/-! # population currency. Lifts E & K to compact switches before Φ. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus FrameBox Cabana Push
open Progress.DirectedRecipe MergeProof Menu Marker Accent Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge}{c f : Side}{Q : Rep G f} {S:StepData c f} {σ κ Λ μ' w t v : ℝ}
variable {V I:Type}[DecidableEq V][Fintype V](R: Marker.Census V) (B:Bands R Q)
-- transforms.BY separate.
def scaleQ : Bool → (ℂ →L[ℝ] ℝ)
| false=> Complex.reCLM | true=> Complex.imCLM
def ink : Bool → ℂ
| false=> 1 | true=> Complex.I
lemma tintX (k:Bool): ‖ink k‖=1:=by cases k <;> simp [ink]
lemma stepColor (k:Bool)(c:ℂ):‖scaleQ k c‖≤ ‖c‖ := by cases k <;> first| exact RCLike.norm_re_le_norm c|exact RCLike.norm_im_le_norm c
lemma harvestQ (c:ℂ):∑ i:Bool,(↑(scaleQ i c):ℂ)*ink i=c:=by
   rw [Fintype.sum_bool]; simp [add_comm,scaleQ,ink] -- order edit
lemma framesV {f':Config G f→ℂ}{a:ℝ}{o:Site f}{U:Support f}{P:BudgetPoint} (h:P.Regular U f')(hx:P.supBounds o U f' a)(k:Bool): let f:Config G f→ ℝ:= scaleQ k ∘ f'; P.Regular U f ∧ P.supBounds o U f a:=by
   intro F; let q:= scaleQ k
   have ht (V)(hv): Push.Local.Chart P.order F V:= ((scaleQ k).contDiff.contDiffAt (x:=(fun x=> f' (increment V x)) 0)).comp (f:=fun x=> f' (increment V x)) _ (h.smooth V hv)
   refine ⟨⟨fun V W h'=> congr_arg q (h.sites V W h'), q.continuous.measurable.comp h.borel,fun i V=> congr_arg q (h.symmetry i V),ht,fun V h a l hl=> Next.Foundations.left_has a hl (ht V h)⟩,hx.1,fun V hv l hl hL=> ?_⟩
   unfold F; rw [Push.Local.left_linear _ _ (h.smooth V hv) hl]; exact (stepColor _ _).trans (hx.2 V hv l hl hL)
lemma stratum {S:Support f} (V: Config G f)(k:Bool)(t:ℝ)(p:Config G f→ℂ): masked t S (scaleQ k ∘ p) V= scaleQ k (masked t S p V):=by
   by_cases h:Healthy t S V; · rw [masked_eq _ _ _ _ h, masked_eq _ _ _ _ h]; rfl
   rw [masked_ne _ _ _ _ h, masked_ne _ _ _ _ h,map_zero]
-- form raw Leaf on ANY blank.Q θ.
omit [Fintype V]
open AbsoluteSums Ovens Ovens.Pipes
lemma blanked (hz: HasSlots Q.p Q.activities)(X:RegularAddress f) (j:ℕ): Q.activities.reg (blankRow f (X,j))=X:=by
    rw [hz.reg]; exact congr_arg Prod.fst (recorded _ _ _)
variable (Q) (X:RegularAddress f)(J:ℕ)(Y:Config G f→ ℝ)(P:BudgetPoint)
local notation "i!"=> blankRow f (X,J)
structure Sale (P:BudgetPoint)(X:Support f)(Y:Config G f→ℝ)(w:ℝ):Prop where
   reads: UsesFinal P.threshold X Y
   gauge: GaugeInvariant Y
   meas: Measurable Y
   norm: ∀ V,‖Y V‖ ≤ w
   marks: ∀ V,Y V≠0→ Healthy P.threshold X V
-- may use negative marker budgets etc.
lemma supportQ {f': Config G f→ℝ} {U:Support f} (x:Site f)(h:P.Regular U f')(hx:P.supBounds x U f' w) : Sale P U (masked P.threshold U f') w:=by
    refine ⟨fun V W hv ht=> ?_,fun i V=>?_,masked_measurable _ _ _ h.borel,fun V=>?_,fun V h=> Classical.byContradiction (fun he=>h (masked_ne _ _ _ _ he))⟩
    · have hh:Healthy P.threshold U V↔Healthy P.threshold U W:=by unfold Healthy; simp_rw [Finset.disjoint_iff_inter_eq_empty,ht]
      by_cases hT:Healthy P.threshold U V; · rw [masked_eq _ _ _ _ hT,masked_eq _ _ _ _ (hh.1 hT)]; exact h.sites V W hv
      rw [masked_ne _ _ _ _ hT,masked_ne _ _ _ _ (fun h=>hT (hh.2 h))]
    · by_cases ht:Healthy P.threshold U V
      · rw [masked_eq _ _ _ _ (show Healthy P.threshold U (gauge i V) from by unfold Healthy; rwa [gauge_flags]),masked_eq _ _ _ _ ht]; exact h.symmetry i V
      rw [masked_ne _ _ _ _ (show ¬Healthy P.threshold U (gauge i V) from by unfold Healthy; rwa [gauge_flags]),masked_ne _ _ _ _ ht]
    by_cases ht:Healthy P.threshold U V
    · rw [masked_eq _ _ _ _ ht]; exact hx.2 _ ht [] (by simp) (by simp)
    rw [masked_ne _ _ _ _ ht,norm_zero]; exact hx.1
-- no flags rewarded omitted. unknown exterior H.P must only give local.Mask.Gates.No Halo extension.
def salesZ (M:R.Mode) (h:M.val.Nonempty)(w:ℝ)(b:ℂ)(hs:Sale Q.p X.support Y w)(hx:HasSlots Q.p Q.activities): Menu.Hat R Q:= by
   refine ⟨{turn:= Lotus.Wing.logKey i!
            ingredient:=Y
            scopedR:=?_
            grant:=fun V h=>?_
            blank:=hx.regular (X,J)
            weight:=w
            earn:=hs.norm
            glows:=hs.gauge
            borel:=hs.meas},M,h,b⟩
   · change UsesFinal Q.p.threshold (Q.activities.reg (i!)).support Y; rw [blanked hx]; exact hs.reads
   change Healthy Q.p.threshold (Q.activities.reg (i!)).support V; rw [blanked hx]; exact hs.marks V h
lemma birthZ (M:R.Mode) (h:M.val.Nonempty)(w:ℝ)(b:Bool)(r:V→ℝ)(hs:Sale Q.p X.support Y w)(hx:HasSlots Q.p Q.activities): let F:= salesZ Q R X J Y M h w (ink b) hs hx; F.M.turn=.logKey i! ∧ F.M.crest=X.support ∧(∃ y:ℝ, y=w ∧ F.M.weight=y)∧ F.s=M ∧ sumFee F r=Marker.Poly.toll r M ∧ ∀ V, Menu.amount F V= Poly.send M ((↑(Y V):ℂ)*ink b):=by
    intro F; have he:F.M.crest=X.support:= congr_arg RegularAddress.support (Port.blanked hx _ _)
    refine ⟨rfl,he,⟨_,rfl,rfl⟩,rfl,?_, fun V=>Menu.varnish ..⟩
    unfold sumFee; change _*‖ink b‖= _; rw [tintX,mul_one];rfl
-- numbers.No compression multi.Value normalization.H.In assigns Foi.B.Role.Ans.
-- include geom.
open Push.AbsoluteSums
lemma ancestry {m n:ℕ}(F:Config G f→ ℝ)(M:R.Mode) (h:M.val.Nonempty)(w:ℝ)(b:Bool)(hs:Sale Q.p X.support (masked Q.p.threshold X.support F) w)(hx:HasSlots Q.p Q.activities)(hh:Q.p.Regular X.support F)(hv:Q.p.supBounds X.site X.support F w)(hK:∃ t≤n,FrameBox.Polynomial t κ X.site m F) : Fan.Mind (salesZ Q R X J (masked Q.p.threshold X.support F) M h w (ink b) hs hx|>.M) F κ m n := by
    let u:= salesZ Q R X J (masked Q.p.threshold X.support F) M h w (ink b) hs hx
    have he:u.M.crest=X.support:= (birthZ Q R X J _ M h w b (fun _=>0) hs hx).2.1
    change Fan.Mind u.M _ _ _ _
    refine ⟨⟨_,show u.M.turn=.logKey i! from rfl⟩,?_,⟨(i!),rfl,?_,he.symm ▸ hh,?_⟩⟩
    · rw [he];rfl
    · rw [he,blanked hx]; exact hv
    rw [blanked hx]; exact hK
end YM.LocalLTE.Port
