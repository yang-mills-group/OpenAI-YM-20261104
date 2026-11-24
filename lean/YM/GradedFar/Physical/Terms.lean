import YM.GradedFar.Physical.Appears

/-!
# Keep joint test, same viewer/phases/o in integrating the discrepancy:
 include the mass of the **actual** test
-/
namespace YM.FVA2.GradedFar.Physical.Tasks
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics MeasureTheory
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window
open OPE Orbits Logged Physical.Round
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h k j t p : ℕ} {I V:Type} {d : Fin n → ℕ}{e: Fin m→ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (K : FramesH P)
    (Q : Reader U.sector.derivatives U.sector.turns U.room.kernel.spin) (θ:ℝ→ℝ)
variable {X:Set (Points n)}{Y:Set (Points m)} [TopologicalSpace I]
  (D:Data U X Y I)
variable [MeasurableSpace I] [OpensMeasurableSpace I] [CompactSpace I]

/-- Test a *pair* of rows. May use e.g. `V=ℂ`, complex multiplication.
 Price then measured with ‖B‖. `variation` is total variation (complex measures allowed).
-/
def Invoice [NormedAddCommGroup V] [NormedSpace ℝ V] (φ:VectorMeasure I V) (B:ℂ→L[ℝ] V→L[ℝ] ℂ) (C:ℝ) (X Y:I→ℂ) :=
    φ.Integrable X ∧ φ.Integrable Y ∧
      ‖(∫ᵛ x, X x ∂[B; φ]) - (∫ᵛ x, Y x ∂[B; φ])‖ ≤ C*‖B‖* φ.variation.real univ

/-- All the following rows keep weights of c, c_W, this integral and every Far
 price. Approx prices (ignore some factor constants). Uniform as in M.3. Tested
 at same viewer and any Alt centre and all unit-ball inputs; shape maps `Data`
 are continuous on compact domains (no shape-related Jacobian incurred, because we DON'T
 move the test to the dilated shape coords); faithful total variation. Profiles:
 for precision we include proof of integrability, together with each estimate.
 Cube estimates permit sharper norm-on-duals separately; here price each output test.
-/
def joint (h p k:ℕ) (η:ℝ)(w:Continuation.Window) (u:Inputs G d)(v: Inputs G e) (C:ℝ) :=
    let i t:= (D.viewer,D.o t)
    let y t:= Ywide U K w (i t) (D.x t) (D.y t) u v
    let r t:= crop p (θ w.len) (Yx N M (D.x t) (D.y t) u v w.sep)
    let u' t (a:Sec G h):= Dwide U K w (i t) (D.y t) v a
    let v' t (a:Sec G h):= crop p (θ w.len) (Dx N M (D.y t) v w.sep a)
    let c t:= cActual N (D.x t) u h p (θ w.len)
    let cW t:= packet U K Q d h w.len (i t) (D.x t) u
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E], ∀ (φ:VectorMeasure I E) [IsFiniteMeasure φ.variation]
      (B:ℂ→L[ℝ] E→L[ℝ] ℂ),
       let L:= Invoice φ B (C*Continuation.Stretch.till G k h η w)
       L y r ∧ (∀ a, Ball 1 a→ L (fun t=>u' t a) (fun t=>v' t a)) ∧
          L (fun t=>y t-r t) (fun t=>u' t (c t)-v' t (c t)) ∧
          L y (fun t=>u' t (c t)) ∧ L y (fun t=>u' t (cW t))

open private cont_crop from YM.GradedFar.Joint
variable {η B C c L L':ℝ}
variable (hX:IsCompact X)(hx:X⊆conf n)(hY:IsCompact Y)(hy:Y⊆Outside m)
-- threshold independent D; can vary center between calls including as function of profile
private lemma price_parts (a b c d e:ℂ){L u:ℝ}(h:0≤L)(hx: ‖a‖+‖b‖+L+‖c‖+‖d‖+‖e‖≤u):
    ‖a‖≤u ∧ ‖b‖≤u ∧ ‖c‖≤u ∧ ‖d‖≤u ∧ ‖e‖≤u := by
    have ha := norm_nonneg a; have hb:= norm_nonneg b; have hc:=norm_nonneg c; have hd:=norm_nonneg d; have he:=norm_nonneg e; refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith only [hx,h,ha,hb,hc,hd,he]
include H hX hx hY hy
set_option maxHeartbeats 400000 in
theorem retained 
    {t p h : ℕ}(H' : Tolerates N M U K Q θ d e X Y t h p c C η B L L') : ∃ T : ℝ,0<T ∧ ∀ᶠ (w:Continuation.Window) in windows (band G c C B),
      ∀ (D:Data U X Y I), ∀ (u:Inputs G d), Within L u →∀ (v: Inputs G e), Within L' v → joint N M U K Q θ D h p t η w u v T := by
   obtain ⟨R,hR,H'⟩:= H'; let X': Set (Points 1):={0}; have h1:X'⊆conf 1:= singleton_subset_iff.mpr fun _ _ _=>Subsingleton.elim ..
   refine ⟨R,hR,?_⟩; filter_upwards [H',entitled hX hx hY hy (band G c C B),entitled isCompact_singleton h1 hY hy (band G c C B), (windows_separation _).eventually (eventually_conf hX hx hY hy),(windows_short _).eventually (booked_margins U Q hX hx h)] with w hw he hi hH hp D u hu v hv
   unfold joint; intro i F P Y Y' c cW E _ _ φ _ B L
   let o t:=(D.viewer,D.o t); have he' j: Injective (beside (atPos (Window.len w) (D.o j) (0:Points 1)) (atPos (Window.Coarse w) (D.o j) (D.y j))) := hi 0 (mem_singleton _) _ (D.tall j) _
   have hf : Continuous F:= stager U K D.viewer D.o D.ox D.x D.ax D.y D.ay w u v (fun j=> he _ (D.lived j) _ (D.tall j) _)
   have hP : Continuous P:= cont_crop _ _ (cont_full H _ _ D.ax D.ay _ (fun j=>hH.1 _ (D.lived j) _ (D.tall j)) u v) _
   have ha (j:Sec G h):Continuous (fun i=> Y i j):= central U K D.viewer D.o D.ox D.y D.ay w v (fun _=>j) (fun _=> continuous_const) he'
   have hD (j:Sec G h):Continuous (fun i=> Y' i j):= by
      unfold Y' Dx; simp_rw [responses_eq]; refine cont_crop _ _ (cont_full H (fun _=> (0:Points 1)) D.y continuous_const D.ay _ (fun j=>hH.2 _ (D.tall j)) _ _) _
   have hΓ (f:I→Sec G h)(h:∀ j,Continuous (fun i=>coord j (f i))) : Continuous (fun i=>Y i (f i)):= central U K D.viewer D.o D.ox D.y D.ay w v f h he'
   have hc (j):Continuous (fun i=>coord j (c i)):=by unfold c; simp_rw [coord_actual]; exact cont_crop _ _ (cont_series H D.x D.ax (fun i=>hx (D.lived i)) u (flash j)) _
   have hx0:Continuous (fun i=>Y i (c i)):=hΓ c hc
   have hx1:Continuous (fun i=>Y i (cW i)):=hΓ cW (fun j=> (continuous_apply j).comp (packet_cont U K Q D.viewer D.o D.ox D.x D.ax _ u (fun i=> hp _ (D.lived i) _)))
   have hx2:Continuous (fun i=>Y' i (c i)) := by
      let X t (j: Toon G h):= crop p (θ (Window.len w)) (DX N M j (D.y t) v (Window.sep w)); have he i:Y' i (c i)=∑ j:Toon G h,coord j (c i)*X i j:=by unfold X c; simp_rw [coord_actual, Y', charged_identity]
      simp_rw [he]; exact continuous_finsetSum _ fun j _=> (hc j).mul (cont_crop _ _ (cont_center H D.y D.ay _ (fun i=> hH.2 _ (D.tall i)) v j) _)
   let C':=R* Continuation.Stretch.till G t h η w
   have hA (j:I)(a: Sec G h)(hg:Ball 1 a):
      ‖F j-P j‖+‖Y j a-Y' j a‖+weigh h (fun p=>Y j p-Y' j p)+ ‖F j-P j-(Y j (c j)-Y' j (c j))‖+‖F j-Y j (cW j)‖+‖F j-Y j (c j)‖ ≤ C':=
      hw (D.viewer,D.o j) _ (D.lived j) _ (D.tall j) u hu v hv a hg
   have hz (a:Sec G h) j : 0 ≤ weigh h (fun p=>Y j p-Y' j p):=by unfold weigh; positivity
   have hg j:= hA j 0 (fun _=>by rw [map_zero]; simp)
   refine ⟨pair_integral φ B hf hP _ ?_,fun i hi=>pair_integral φ B (ha i) (hD i) _ ?_,pair_integral φ B (hf.sub hP) (hx0.sub hx2) _ ?_,pair_integral φ B hf hx0 _ ?_,pair_integral φ B hf hx1 _ ?_⟩
   · intro j; exact (price_parts _ _ _ _ _ (hz 0 j) (hg j)).1
   · intro j; exact (price_parts _ _ _ _ _ (hz 0 j) (hA j i hi)).2.1
   · intro j; exact (price_parts _ _ _ _ _ (hz 0 j) (hg j)).2.2.1
   · intro j; exact (price_parts _ _ _ _ _ (hz 0 j) (hg j)).2.2.2.2
   intro j; exact (price_parts _ _ _ _ _ (hz 0 j) (hg j)).2.2.2.1
end
end YM.FVA2.GradedFar.Physical.Tasks
