import YM.OPE.Compatible.Grout.Pitch
/-!
# Bound R potential reweight used with Touch piece via Sable.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C s : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable {X: Support f}{u v:Config G f→ℝ}
def Shade (R:Rep G f) := ((R.p.B+R.p.B+1:ℕ):ℝ)^4
lemma pint_shade {b : ℝ} (hx:0≤w)(he:0<b)(ha:4*Shade R*w ≤ b)(Y:Support f) : (Real.exp (Y.card*w)-1) ≤ 4*Shade R*w/b * Real.exp (b*coverNumber R.p.B Y):=by
    let q:=Shade R; let z:ℝ:=coverNumber R.p.B Y; let t:ℝ:= Y.card; have hz:0 ≤ z:=by unfold z; positivity
    have hh:t≤z*q:= by unfold t z q Shade; exact_mod_cast Corona.pays Y R.p.B
    have ht: Real.exp (t*w)-1 ≤ Real.exp (t*w)*(t*w):=by
        let a:=t*w; have hp:= Real.add_one_le_exp (-a); have hv:0 ≤ a:= mul_nonneg (Nat.cast_nonneg _) hx; have h:= Real.exp_neg a
        have hz':= mul_le_mul_of_nonneg_left hp (Real.exp_pos a|>.le); rw [h,mul_inv_cancel₀ (Real.exp_pos a|>.ne')] at hz'; linarith
    apply ht.trans; let f:= b*z/2
    have hv : t*w ≤ f:= (mul_le_mul_of_nonneg_right hh hx).trans (by unfold f; unfold q; nlinarith only [ha,mul_le_mul_of_nonneg_left ha hz, mul_nonneg he.le hz])
    apply le_trans (mul_le_mul_of_nonneg_right (Real.exp_monotone hv) (mul_nonneg (Nat.cast_nonneg _) hx))
    calc
       Real.exp f*(t*w) ≤ Real.exp f*( (2*q*w/b) * f):=by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
          apply (mul_le_mul_of_nonneg_right hh hx).trans_eq; unfold f; field_simp
       _ ≤ Real.exp f *((4*q*w/b)* Real.exp f):=by
         have hF:0≤f:= by unfold f; positivity
         have hx:q≥0:=by unfold q Shade; positivity
         have ht:2*q*w/b ≤4*q*w/b:=by gcongr; linarith
         exact mul_le_mul_of_nonneg_left (mul_le_mul ht (by linarith [Real.add_one_le_exp f]) hF (by positivity)) (Real.exp_pos _).le
       _ = _ := by rw [mul_left_comm,← Real.exp_add, show f+f=b*z by unfold f; ring]
section
variable (hR:R.Lawful σ C Λ E w)
include hR
lemma smudge_env (X:Support f) : Envelope (smudge R X):=by
   obtain ⟨h,H⟩:= sheer hR (fun _=>1) (Envelope.const _) X
   exact ⟨Measurable.tsum h, H.bound⟩
omit hR
variable {t v c' K:ℝ}{V:Config G c} (hx:Besotted R S t K V w)(hp:0≤t)(hv:0≤K)(hh:0≤ S.push R.beta R.eval V)(hw:0≤w)(h:0<a)(he:4*Shade R*w ≤ a)
local notation "X₀"=> Real.exp ((t+a)*coverNumber R.p.B X)*(4*Shade R*w/a)*K*S.push R.beta R.eval V
include hx hp hv hh hw he h
lemma pint_pays (hs:PaidY R S X m u c')(hX:X.Nonempty) : ‖S.push R.beta (fun U=>smudge R X U * u U) V‖ ≤ X₀*(Real.exp ((t+a)*m)*c'):=by
    obtain ⟨Y,hL,hu,hy⟩:= hs
    have ht:=hx X Y hL (hX.mono hL) u c' hu; apply ht.trans; let f:=4*Shade R*w/a
    have hf:0≤f:=by unfold f Shade; positivity
    let y:=coverNumber R.p.B Y; let x:=coverNumber R.p.B X; let D:=S.push R.beta R.eval V
    have hz : y ≤ x + m:=by have hz:=hy X le_rfl; rwa [Finset.union_eq_right.mpr hL] at hz
    have hg : Real.exp (t*y)*(Real.exp ((Y.card:ℝ)*w)-1) ≤ f* (Real.exp ((t+a)*x)*Real.exp ((t+a)*m)):=by
        apply (mul_le_mul_of_nonneg_left (pint_shade hw h he Y) (Real.exp_pos _).le).trans; rw [mul_left_comm,← Real.exp_add,← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ hf
        apply Real.exp_monotone; have hy:=mul_le_mul_of_nonneg_left (show (y:ℝ) ≤ (x:ℝ)+m by exact_mod_cast hz) (add_nonneg hp h.le); unfold y at *; linarith
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hg hv) hh) hu.safe).trans_eq; unfold f x; ring
include hR
lemma vast (hk:X.Nonempty)(hK: S.IsKernel R.beta G)(hs:Sable R S X (t+a) u v): ‖S.push R.beta (fun U=>smudge R X U*u U) V‖ ≤ X₀*v:=by
    obtain ⟨ι,hι,J,m,b,hh',hr,H⟩:=hs
    have hy:= Sable.fine hh' hr (add_nonneg hp h.le)
    let p(i:ι) (U) := smudge R X U * J i U
    have he' i:Envelope (p i):=(smudge_env hR X).mul (hh' i).owns
    obtain ⟨q,hq⟩:=(smudge_env hR X).cost
    have hm : Dominated p:= ⟨_,hy.2.1.mul_left q,fun i U=> by unfold p; rw [norm_mul]; exact mul_le_mul (hq _) ((hh' i).cash U) (norm_nonneg _) ((norm_nonneg _).trans (hq U))⟩
    rw [show (fun U=>smudge R X U*u U)=fun U=>∑' i,p i U from funext fun U=> ((H U).mul_left _).tsum_eq.symm,← (push_Real hK hm (fun i=>(he' i).meas) V).tsum_eq]
    have hY:0 ≤ Real.exp ((t+a)*coverNumber R.p.B X)*(4*Shade R*w/a)*K*S.push R.beta R.eval V:=by unfold Shade; positivity
    have hb:=budget_mono (budget_scale hY hr) (fun i=>norm_nonneg _) (fun i=>pint_pays hx hp hv hh hw h he (hh' i) hk)
    exact (norm_tsum_le_tsum_norm hb.2.1).trans hb.2.2
end
end YM.PhysicalNext.Repeat.Aroma
