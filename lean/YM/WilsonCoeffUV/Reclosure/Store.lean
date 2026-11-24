import YM.WilsonCoeffUV.Vacuum.UV.Choices
import YM.WilsonCoeffUV.Reclosure.Technical
/-! Optional curvature post charge. Bind to structural choices, not hidden extra Beta inputs
for perturbative recursion. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Near PowerSeries Supply Ticket Realm Next.Foundations
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{c:Side}{N M e m i k r t:ℕ}{s S a b u v:ℝ}{W X F:Canvas G}{Ñ:ChartRatio G} {A:Levels G}
open Real

def chapeau (K:KernelChoices)(e r:ℕ)(Ñ:ChartRatio G):ℝ:= (eventually_atTop.mp (strawShelf K e r Ñ)).choose
def accountZ (K:KernelChoices)(F:ℕ→ℕ)(Ñ:ChartRatio G)(j:ℕ) : ℝ:=Real.exp (exp (chapeau K (F j) j Ñ))
variable {p:Sheet G}{Q:Rolls p}{Ω:Protection Q}{H:ℕ→ℕ} {Y:Delays Ω}{o:Bar Y}{b': Wait o}
lemma proceeds (g:G.Simple)(hA:LocalRatio Ñ)(pL:floors G p.kernel H≤ p.floorL)(a:Paid b' A)(hp:voucher Q H Ñ ≤ Y.betaEntry)(hz:accountZ p.kernel H Ñ ≤ Y.betaEntry)(hv:Tendsto H atTop atTop)(i:ℕ): ∀ᶠ ℓ :ℕ in atTop,∃ R:Realm G i Credit.leanC,R.draws=A ∧ R.paid=Ñ ∧ R.y=zz A ∧ R.anchor=ℓ ∧ Inkplate i R Credit.leanC :=by
    have he:Tendsto (fun i=> A.clock.J (i+1)) atTop atTop:= A.fits.deep.comp (tendsto_add_atTop_nat 1)
    obtain ⟨ℓ,hT⟩:= eventually_atTop.mp ((he.eventually_ge_atTop 5).and ((hv.comp he).eventually_ge_atTop i)); apply (eventually_ge_atTop ℓ).mono; intro q hq
    let m h (p':q≤h):= quest A h Ñ ((hT h (hq.trans p')).1) (afforded a.kernel a.lengths H pL h (hT h (hq.trans p')).1)
    have hu k (hv:q≤k): delayCost Q H Ñ (A.clock.J (k+1)) ≤ zz A k:= (escalator (le_trans (hp _) (a.pays k))).2.2
    have hx k (v:q≤ k): Escrow (m k v) i (Credit.leanC.buy (zz A k)):=by
        rw [Credit.lean_cost]; let j:=A.clock.J (k+1); have h : A.S.block k=Q.L j:=by rw [←A.fits.sameFactor,a.lengths]
        exact further ((eventually_atTop.mp (deferred p.kernel (Q.L j) j (H j) Ñ)).choose_spec _ (hu k v) A k a.kernel rfl h _ _) (hT _ (hq.trans v)).2 le_rfl
    obtain ⟨u,v,_⟩:= install_awards g hA pL a hp q i (fun k hk=>hT k (hq.trans hk))
    have H' k (v:q≤ k):@aftB G A k (H (A.clock.J (k+1))) Ñ (zz A k) (hT k (hq.trans v)).1 (afforded a.kernel a.lengths H pL k (hT k (hq.trans v)).1) := by
        let j:= A.clock.J (k+1)
        have hx: exp (exp (chapeau p.kernel (H j) j Ñ)) ≤ A.clock.hatBeta k:= (hz j).trans (a.pays k)
        have he:= Real.log_le_log (show 0 < exp .. from exp_pos _) hx
        rw [Real.log_exp] at he; have hv:= Real.log_le_log (exp_pos _) he; rw [Real.log_exp] at hv
        apply (eventually_atTop.mp (strawShelf p.kernel (H j) j Ñ)).choose_spec _ (le_trans hv (le_add_of_nonneg_left zero_le_one)) A k a.kernel rfl
    let R : Realm G i Credit.leanC:= ⟨A,Ñ,g,hA,q,zz A,u,v,m,fun k p=> le_rfl,hx⟩
    refine ⟨R,rfl,rfl,rfl,rfl, ?_⟩
    constructor
    · intro m b k hk; unfold cash; rw [Credit.lean_cost]; exact (H' m b k (Nat.le_trans hk (Nat.add_le_add_right (hT m (hq.trans b)).2 _))).1
    intro m b k hk; unfold cash; rw [Credit.lean_cost]; exact (H' m b k (Nat.le_trans hk (Nat.add_le_add_right (hT m (hq.trans b)).2 _))).2
end YM.WilsonCoeffUV.Bank.Mosaic
