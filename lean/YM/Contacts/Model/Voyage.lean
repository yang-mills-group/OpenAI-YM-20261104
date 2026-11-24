import YM.Contacts.Model.Fork
noncomputable section
namespace YM.Contacts.Model
open Function Lattice Finset Filter Set PhysicalNext.Repeat Pressure Wilson MeasureTheory RG
open Slide (Stars)
open Trio (froth Mirrors Offer)
open AnalyticBridge VerifiedReset Push.AbsoluteSums Animals Stationary Milling PertExtension.Series Exterior Precision Ion
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n m c C:Side}{k w r z:ℕ}
open Push.Uniform Work.F02 Metric
variable {Z μ b C' Λ : ℝ}{s:PlaqAxes}{r : ℕ}{x:Site m}
section rows
-- port for any ball centered around identity. no P.c).
variable (p:Clip)(R:PathData G){K:Type}[NormedAddCommGroup K][NormedSpace ℝ K]{U: K→ Config G m}{y:K}{X:Set K}
def pole (μ:ℝ)(w:ℕ):= Real.exp (-μ/2*w)
def pullLength (r:PlaqAxes)(j:ℕ):=(R.row r j).2.length
variable {p} (V:Set ℕ)(x:Site m)
def startAt (a:PlaqAxes)(U:Config G m): G.Color := ∑' j:↥V,R.ellTerms (x,a) j U
def title (F:ℕ→Atom G r)(U:Config G m) :=∑' i:↥V,(F i).unmasked U x
lemma start_ana (a:PlaqAxes)(he : ∀ i,ContDiffAt ℝ ω (fun y=>G.mat (U y i)) y) (h: R.Bounds p μ C' Λ): ContDiffAt ℝ ω (startAt R V x a ∘ U) y := by
   let A:=U y; let Φ(Z:Ambient G m):= ∑' i:↥V, rowExt R (x,a) i.val Z
   have ht: AnalyticAt ℂ Φ (physical A):= by
     refine analytic_series _ (radius_pos h.width) (fun i=> (((slotExt_contDiff (R.row a i.val).2 x).const_smul ((R.row a i.val).1)).differentiable (by simp))) ((h.rows a).2.1.subtype V|>.mul_right (slotConst G)) ?_ -- end
     intro i Z hZ; unfold rowExt; rw [norm_smul,Real.norm_eq_abs]; exact (mul_le_mul_of_nonneg_left (slotExt_bound A h.width Z (ball_subset_closedBall hZ) _ x) (by positivity : 0 ≤ |(R.row a i.val).1|)).trans_eq (by simp only [Function.comp_apply]; ring)
   have hF v: colorReal G (Φ (physical (U v)))=startAt R V x a (U v):= by
      rw [show Φ (physical (U v))= colorUp G (startAt R V x a (U v)) from ?_,colorReal_up]
      unfold Φ startAt; rw [(colorUp G).map_tsum (show Summable (fun j:↥V=> R.ellTerms (x,a) j.val (U v)) from ((R.ell_dominated h (x,a)).summable (U v)).subtype (·∈ V))]; refine tsum_congr fun i=> ?_
      rw [rowExt,slotExt_physical,PathData.ellTerms,map_smul]
   have hh:= ((ht.contDiffAt.restrict_scalars ℝ).comp y (physical_contDiffAt he)); apply ((colorReal G).contDiff.contDiffAt.comp (f:= Φ∘ fun y=> physical (U y)) y hh).congr_of_eventuallyEq (Eventually.of_forall fun v=> (hF v).symm)
lemma grains (F: ℕ→Atom G r)(hs:0<μ)(hf:SumBudget (fun i=>(F i).budget μ) C')(U:Config G m): Summable fun i=> (F i).unmasked U x:= Summable.of_norm_bounded (hf.2.1.mul_right ((2:ℝ)^r)) (fun i=> ((F i).unmasked_bound U x).trans (mul_le_mul_of_nonneg_right ((F i).lower_budget μ hs) (by positivity)))
lemma stem_ana (F:ℕ→Atom G r)(hs:0<μ)(hf:SumBudget (fun i=>(F i).budget μ) C')(he :∀ i,ContDiffAt ℝ ω (fun y=>G.mat (U y i)) y): ContDiffAt ℝ ω (title V x F ∘ U) y:= by
   let A:=U y; let Φ(X:Ambient G m):= ∑' i:↥V, atomExt (F i.val) x X
   have ht:AnalyticAt ℂ Φ (physical A):= analytic_series _ (radius_pos hs) (fun i => (atomExt_contDiff _ _).differentiable (by simp)) (hf.2.1.subtype V|>.mul_right ((slotConst G)^r)) (fun i y hy=>atomExt_bound (F i.val) _ hs _ (ball_subset_closedBall hy) x)
   have hF v: Complex.reCLM (Φ (physical (U v)))=title V x F (U v):= by
      rw [show Φ _= Complex.ofRealCLM (title V x F (U v)) from ?_]; rfl
      unfold Φ title; rw [Complex.ofRealCLM.map_tsum (show Summable (fun j:↥V=> (F j.val).unmasked (U v) x) from (grains x F hs hf (U v)).subtype (·∈V))]; exact tsum_congr fun i=> atomExt_physical (F i.val) _ x
   have hh:= ((ht.contDiffAt.restrict_scalars ℝ).comp y (physical_contDiffAt he)); exact (Complex.reCLM.contDiff.contDiffAt.comp (f:=Φ ∘ fun v=>physical (U v)) y hh).congr_of_eventuallyEq (Eventually.of_forall fun v=> (hF v).symm)
variable {R} (h: R.Bounds p μ C' Λ)
variable (hO:IsOpen X)(hc:IsPreconnected X)(hx: y∈ X) (ht:∀ i z, z∈X→Allows k (fun y=> G.mat (U y i)) z Z)
def portSize (G : Gauge)(μ Z:ℝ)(k:ℕ):= ‖Work.F02.colorReal G‖* (|Work.F02.slotConst G| *allow Z μ k)
def atomSize (G: Gauge)(μ Z : ℝ)(k r:ℕ) := allow Z μ k * |slotConst G|^r
include hO hc hx ht
include h in
lemma yaw (v:PlaqAxes)(l:ℕ)(hy:∀ i∈V,l≤pullLength R v i) : Allows k (startAt R V x v ∘ U) y ((pole μ l*C')*portSize G μ Z k) := by
   let a i:=|(R.row v i).1|; let L:=pullLength R v; let e(i:↥V):= a i.val*Real.exp ((μ/2)*L i.val); let b:=portSize G μ Z k
   have hh: SumBudget e (pole μ l*C'):= marker a _ (fun _=>abs_nonneg _) _ _ hy (h.rows v) h.width.le
   have hb:0≤ allow Z μ k:=allow_pos (ht (Classical.arbitrary _) y hx|>.nonneg) h.width _; have hB:0≤ b:= by unfold b portSize; positivity
   let f (i:↥V)(p:K):=R.ellTerms (x,v) i.val (U p)
   have he i (y:K)(hx:y∈X): Allows k (f i) y (b*e i):= ( (checkout h.width (fun j=> ht j y hx) x _).smul ((R.row v i.val).1)).mono (by unfold e b L pullLength portSize a; exact le_of_eq (by ring))
   have h':Allows k (fun y=>∑' i,f i y) y (b*(pole μ l*C')):= attendance f _ hO hc hx (budget_scale hB hh) he (start_ana R V x v (fun i=> (ht i y hx).analytic) h)
   rw [mul_comm]; exact h'
lemma yore (F:ℕ→Atom G r)(hs:0<μ)(hf:SumBudget (fun i=> (F i).budget μ) C')(l:ℕ)(hy:∀ i∈V,l≤(F i).length) : Allows k (title V x F ∘ U) y ((pole μ l*C')*atomSize G μ Z k r) := by
   let e(i:↥V):= (F i.val).budget (μ/2); let b:=atomSize G μ Z k r
   have hh:SumBudget e (pole μ l*C'):=marker (fun i=>(F i).magnitude) _ (fun i=> by unfold Atom.magnitude; positivity) _ _ hy hf hs.le; have hB:0≤ b:= by unfold b atomSize; have hb:=allow_pos (ht (Classical.arbitrary _) y hx|>.nonneg) hs k; positivity
   let f (i:↥V)(z:K):=(F i.val).unmasked (U z) x
   rw [mul_comm]; exact attendance f _ hO hc hx (budget_scale hB hh) (fun i y hy=>(rescue hs (fun j=> ht j y hy) x _).mono (show _≤b*e i from (by unfold e b atomSize; exact le_of_eq (by ring)))) (stem_ana V x F hs hf fun i=> (ht i y hx).analytic)
end rows
end YM.Contacts.Model
