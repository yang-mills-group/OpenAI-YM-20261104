import YM.OPE.Compatible.Melon.Gush
/-!
# Orphan order-one gauge determinant in crown
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Glass
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace ENNReal
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial
attribute [local instance] Gauge.frobInner
variable {i:ℕ}{l b:ℝ}{B:Sponsor G}{Q:Seasons B} {A:Alps B Q i l} {H: Even n.val}
local notation "Lf" => Tested.germ
local notation "TK" => Keys G (Limb H)
variable (T:Plot H) (X:Lit H A b) (R:Bor H A b)
local notation "DK" => Keys G T.Stable
local notation "FD" => Keys G T.Free
lemma tall_station: Radial.Stationary (tall T (G:=G)):=by
     let A:=T.skews G; let f:=hippie H (G:=G); have hk:=h_station H (G:=G); have ht : fderiv ℝ f 0=0:=by apply ContinuousLinearMap.ext; intro x;have he:=hk.base1 x; simpa [jet,iteratedFDeriv_one_apply,f] using he
     refine ⟨tall_sane T,?_,fun x=>?_⟩
     · change f (A.gradient 0)=0; rw [A.grad0]; exact hk.base0
     unfold jet; rw [iteratedFDeriv_one_apply,show fderiv ℝ (tall T) 0=fderiv ℝ (f ∘ A.gradient) 0 from rfl,fderiv_comp]; rw [A.grad0,ht];simp
     · rw [A.grad0]; exact hk.smooth.differentiableAt (by simp)
     exact A.gradC.differentiableAt (by simp)
-- positive both ways
lemma tide_rise (x:TK):0 ≤ tall T x := div_nonneg (rainbow_nn _) (by norm_num)
lemma onlyPos {v:TK}(hx:jet (tall T) 2 v=0):0 ≤ jet (tall T) 3 v:=by
     let f:=tall T (G:=G); have he:= (Pawn.trio (tall_station T (G:=G))).stale v; unfold Reads at he; obtain ⟨C,hc,H⟩:= Reads.isTariff.mp he; let a:= jet f 3 v; let b:= jet f 4 v; change 0≤a
     by_contra! h; let U(t:ℝ):= a+t*b+C*t^2; have ht:Tendsto U Lf (𝓝 a):=by convert! (show Continuous U by unfold U; fun_prop).tendsto (0:ℝ)|>.mono_left nhdsWithin_le_nhds; simp [U]
     obtain ⟨t,hy,hp,hD⟩:= ((ht.eventually (eventually_lt_nhds h)).and (H.and Tested.eventually_pos)).exists
     have h: 0 ≤ tall T (t • v) / t^2:= div_nonneg (tide_rise ..) (by positivity)
     let q:= tall T (t • v) / t^2
     change ‖q-((Pawn.mold (tall T) 2 v).atK t)‖ ≤ _ at hp
     rw [show ((Pawn.mold (tall T) 2 v).atK t)= jet (tall T) 2 v+t*a + t^2*b from rfl,hx, Real.norm_eq_abs] at hp; obtain ⟨_,hb⟩:= abs_le.mp hp
     change 0 ≤ q at h; change U t < 0 at hy; have he:= mul_neg_of_pos_of_neg hD hy; unfold U at he; linarith only [he,hb,h]
lemma h_touched (x:FD): jet (tall T) 3 (compass H T G (x,0))=0:=by
     let U:=tall T (G:=G);let v:= compass H T G (x,0); have he:= (flare T (G:=G) x 0); have hp: jet U 2 v=0:= by unfold U v; simp [he]
     have hv: jet U 2 ((-1:ℝ) • v)=0:=by rw [jet_smul,hp,mul_zero]
     have hx:= onlyPos T hp; have ht:= onlyPos T hv; change _ ≤ jet U _ _ at ht; rw [jet_smul] at ht; exact le_antisymm (by change _ ≤ jet U 3 v at hx; change jet U 3 v ≤ 0; linarith) hx
end YM.OPE.Cascade.Glass
