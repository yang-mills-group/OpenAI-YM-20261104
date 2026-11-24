import YM.OPE.Compatible.Waft.An
/-! # Finite leaders over the measured quotient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e t:ℕ}{τ:Phase→ℕ}
namespace PriceZ
variable {W L: Type}
variable {K:Sponsor G}{T: Seasons K}{v:W→ℝ}{P:ChartRatio G}
variable (A:(i':W)→Alps K T i (v i'))(X:W→Side)(H:∀ i,Even (X i).val)(V:∀ i,Plot (H i))
local notation "Y" j=>Libra.Keys G (Stand.Free (V j))
-- Nom
variable {q:W→ℝ}
abbrev TokenV (p:Script (Shade G) k)(H:Even c.val)(X:Plot H)(x:Libra.Keys G (Stand.Free X)):= (k.factorial:ℝ)⁻¹ * narrate c p (spool G c (rayS H X G x))
lemma valBill (H:Even c.val)(X:Plot H)(p:Script (Shade G) k)(x:Libra.Keys G (Stand.Free X))(a:ℝ)(h:soot 0 p a): ‖TokenV p H X x‖ ≤ (k.factorial:ℝ)⁻¹ * ((c.val:ℝ)^4 *a*‖x‖^k) :=by
    unfold TokenV; rw [norm_mul, Real.norm_of_nonneg (by positivity)]; refine mul_le_mul_of_nonneg_left ?_ (by positivity); let y:= spool G c (rayS H X G x); apply (norm_sum_le ..).trans; apply (Finset.sum_le_sum (g:=fun _=> a*‖x‖^k) (fun i _=>?_)).trans; rw [Finset.sum_const,Finset.card_univ,Lattice.site_card,nsmul_eq_mul,Nat.cast_pow,mul_assoc]; exact (hem h i y).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (ray_norm ..) _) h.coins)
lemma S_jet (z:W)(x:Y z)(k:ℕ):
   jet (swornV (A z).clip (A z).live) k (rayS (H z) (V z) G x)= TokenV ((A z).word k) (H z) (V z) x ∧ jet (swornY (A z).live) k (rayS (H z) (V z) G x)= TokenV ((A z).liftZ k) (H z) (V z) x:=by
       let y:=rayS (H z) (V z) G x; have he:= ((A z).fullK k).wink (X z) k le_rfl (fun _=> y); have hv:= ((A z).fullL k).wink (X z) k le_rfl (fun _=> y); exact ⟨congr_arg ((k.factorial:ℝ)⁻¹ * ·) he.symm,congr_arg ((k.factorial:ℝ)⁻¹ * ·) hv.symm⟩ -- eq orientation
lemma parentArt (p:W→Script (Shade G) k)(a:ℝ)(ha:0≤a)(hv:0 ≤ q)(h:∀ i, soot 0 (p i) (a*q i)): WindZ X 4 k q fun j x=>TokenV (p j) (H j) (V j) x:=by
    refine ⟨⟨(k.factorial:ℝ)⁻¹ * a,by positivity,fun i x=>?_⟩,fun i=>?_⟩
    · apply (valBill _ _ _ _ _ (h i)).trans; have hg: 0≤ q i:=hv i; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg x) (le_add_of_nonneg_left (a:=‖x‖) zero_le_one) k) (by positivity)) (show 0≤(k.factorial:ℝ)⁻¹ by positivity)); unfold care; apply le_of_eq; ring
    let L:=(spool G (X i)).toContinuousLinearMap ∘L rayS (H i) (V i) G; let y(z:Site (X i))(x:Y i):= Flume.Script.value z (p i) (L x); refine (Bond.keep _).mul (Bond.sum y Finset.univ (fun i' _=>?_)); let g:=orchestra (p i) i'; rw [show y i'=(fun x:Y i=> g (fun _=> L x)) from ?_]; exact Bond.multiline g (fun _=>L) (fun a f=> Bond.glyph (f.comp L.toLinearMap)); funext x; exact (instruments _ (sootS (h i)) ..).tsum_eq
lemma pegV {s:Clip}(hp:∀ i,(A i).clip=s)(k:ℕ): WindZ X 4 k 1 fun j x=> jet (swornV (A j).clip (A j).live) k (rayS (H j) (V j) G x):=by
      simp_rw [fun j x=>(S_jet A X H V j x k).1]; obtain ⟨a,ha,h⟩:=word_cost K T i k 0 s; apply parentArt X H V _ a ha zero_le_one; intro i; simpa only [Pi.one_apply,mul_one] using! h _ (A i) (hp i)
lemma pegW (k:ℕ)(a:ℝ)(hv:∀ i, v i≤ a)(ha:0≤ a)(hp:0≤v): WindZ X 4 k 1 fun j x=> jet (swornY (A j).live) k (rayS (H j) (V j) G x):=by
      simp_rw [fun j x=>(S_jet A X H V j x k).2]; obtain ⟨b,hb,h⟩:=leaf_cash K T i k 0; apply parentArt X H V _ (b*a) (mul_nonneg hb ha) zero_le_one; intro i; apply (h _ (hp i) (A i)).tips; rw [Pi.one_apply,mul_one]; exact mul_le_mul_of_nonneg_left (hv i) hb
end PriceZ
end YM.OPE.Quit
