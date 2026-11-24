import YM.OPE.Compatible.Draft.Gong
/-!
# All coherently transported in finite-reg History. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{n c f:Side}
open Wilson RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp Pilot
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial Flock Metric Glass
attribute [local instance] Gauge.frobInner
variable {i j:ℕ}{l b:ℝ}{B:Sponsor G}{Q:Seasons B} {S: StepData c f}{H: Even c.val}
local notation "μ"=> even_both S.ratio H
local notation "J!"=> Rill.rollB S H
variable {A:Alps B Q i l}{Y: Bor (even_both S.ratio H) A b} (t:S.Choices) (h:S.patch.Branches S.kernel G) {V: ChartRatio G}
def Uses (L:(Tableau S H).Stand ({origin μ}:Set _)) (T: Lid G L.Free) (A:Alps B Q i l) (b:ℝ) :Prop := T.f =ᶠ[𝓝 0] worldF S H t A ∘ L.rollX ∧ T.w =ᶠ[𝓝 0] worldW S H t b A ∘ L.rollX
include h
lemma loom0 (V:ChartRatio G)(U:Plot (even_both S.ratio H))(Z: Bor (even_both S.ratio H) A b)(Y:Lid G (StemX S H U).Free)(he: Uses t (StemX S H U) Y A b)(p:ScriptJ (Keys G U.Free))(hp:p.B)(hV:LocalRatio V): Y.pay V (fun x=> p (prL (piBond S H U) G x))=(Z.L U).pay V p := by
      obtain ⟨u,hu,hx⟩:= bravePQ S H U t h; obtain ⟨ha,hq⟩:=stems U t Z hu hx h; let P:=piBond S H U; have hz:Tendsto (hu.crown P) (𝓝 0) (𝓝 0):=by simpa only [Dimes.grad0] using! (hu.suite P).gradC.continuousAt.tendsto
      exact hu.alone P (Z.L U) (wellX S H b) Y ((he.1.comp_tendsto hz).trans ha) ((he.2.comp_tendsto hz).trans hq) hV p hp
lemma loft (x y:Keys G J!)(k:Tile G (Node μ))(hp:(Tableau S H).dress k (put x)=put y): worldF S H t A x=worldF S H t A y ∧ worldW S H t b A x = worldW S H t b A y :=by
      have hf:(Pond μ).dress k (put (lo_left S H G x))=put (lo_left S H G y):= funext fun i=>congr_fun hp (.inl i)
      obtain ⟨Hf,Hw⟩:= muralG μ A _ _ _ hf
      have hc:noiseC S H t y=noiseC S H t x:=by
           unfold noiseC; have ht:= accom S H (put x) k; rw [hp] at ht; obtain ⟨a,b⟩:=Prod.mk.inj ht; change coat μ (put (lo_left S H G y))=_ at a; change coat H (put (lo_right S H G y))=_ at b; rw [a,b]; exact congr_arg (·/(4:ℝ)) (caring S h (k ∘ crumb μ) _ _ _)
      unfold worldF worldW tintT; rw [Hf,Hw,hc]; exact ⟨rfl,rfl⟩
lemma safeF (A:Alps B Q i l) : ContDiffAt ℝ ω (worldF S H t A) 0:=((((show ContDiffAt ℝ ω _ ((lo_left S H G) 0) from (by rw [map_zero]; exact muralD μ A)).comp 0 (lo_left S H G).contDiff.contDiffAt).sub contDiffAt_const).add (narrated t h))
lemma safeW (A:Alps B Q i l) : ContDiffAt ℝ ω (worldW S H t b A) 0:= ((show ContDiffAt ℝ ω (tintT μ A b) ((lo_left S H G) 0) from (by rw [map_zero]; exact tintD μ A b)).comp 0 (lo_left S H G).contDiff.contDiffAt).mul (((narrated t h).const_smul (-b)).exp)
end YM.OPE.Cascade.Rill
