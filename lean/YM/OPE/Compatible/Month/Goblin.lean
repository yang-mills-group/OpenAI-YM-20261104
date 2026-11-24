import YM.OPE.Compatible.Month.Fiddle
/-!
# Rate of a normalized expectation from a local approximation

`Model.arg` is the normalized expectation of an observable of the selected
coordinates. For a family satisfying `Chase` and the eventual field bound,
`Chase.across` turns the local approximation `BeamN` into a rate bound for
`Model.arg` minus the comparison value. It assumes the stated envelope and growth
bounds, and the error exponent satisfies `e ≥ -11/10`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard AnalyticBridge.VerifiedReset Geo
open Next.Rank.Thirst YM.OPE
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P:Teller G} {D:Patch} {E:ConnectedActivityE6.Target G P} {L:Side} {W a σ C κ v γ t s w:ℝ} {m:ℕ}
variable {o:ConnectedActivityE6.Target.Order G W}
namespace Model
def actual (M:Model D P L E o κ C m)(f:Config G M.f→ℝ):= M.V.push M.R.beta (M.R.eval*f) M.sheet.V / M.V.push M.R.beta M.R.eval M.sheet.V
def arg (M:Model D P L E o κ C m)(I:Seats M.forest)(f:World M.forest I G→ℝ):= M.actual (f ∘ chant M.forest I)
end Model
variable {ι:Type*} {l:Filter ι} {A:ι→ Model D P L E o κ C m}
def BeamN (A:Model D P L E o κ C m)(i:Seats A.forest)(j:Seats A.forest)(h:i⊆j)(n t:ℕ)(f:World A.forest i G→ℝ) (k:A.V.Choices)(u ε:ℝ) :=
    let m₀:=A.R.p.B; let a:=spillMass (G:=G) L n A.x; let b:=spillMass (G:=G) L t A.x
    0≤ ε∧∀ y:World A.forest j G,dazed h a b y→ ‖report i j A.R A.sheet.V m₀ k b f y-u‖≤ ε
-- Propagate the local approximation along the filter.
namespace Chase
variable (h:Chase A l)
include h
theorem across (u:ℕ)(hh:∀ᶠ i in l, ‖(A i).g‖ ≤ spillMass (G:=G) L u (A i).x) :
     ∃ v n:ℕ,∀ t:ℕ, v ≤ t → ∀ (d:ι→ℕ)(_hg:Lite A l (fun i=>(d i:ℝ)))(x:∀ i,Site (A i).c)(I:∀ i,Seats (A i).forest)(p:∀ i,Homer (A i) (x i) (d i) n (I i))
     (f:∀ i,World (A i).forest (I i) G→ℝ)(k:∀ i,(A i).V.Choices)(w b ε:ι→ℝ) (e:ℝ), -(11/10)≤e →
      Wage A l ε e → Wage A l b 0→ Wage A l w 0→
        (∀ᶠ i in l,Envelope (f i)∧ (∀ x,‖f i x‖≤ b i)∧ BeamN (A i) (I i) (p i).H (p i).good.nested v t (f i) (k i) (w i) (ε i)) →
          Wage A l (fun i => (A i).arg (I i) (f i) - w i) e :=by
   obtain ⟨v,hv⟩:=h.terrainM u hh; obtain ⟨n,hn⟩:= h.pilots
   refine ⟨v,n,?_⟩; intro t ht d hd x I p f k w b e s hs he hb hw hx
   obtain ⟨H₀,H⟩:=rosy h d hd x I p b hb
   let B(i):=spillMass (G:=G) L t (A i).x; let a₀(i):=spillMass (G:=G) L v (A i).x
   let τ:=E.ε/2
   let y i:=marksV (A i).R (p i).X P.top.width τ P.top.paths (loopBill G L (A i).x) (barM A i)+2*((p i).X.card*(est (A i).R.p τ*incomingE G L (A i).x))
   let g i:=promotion (A i).R (barM A i) (p i).X (incomingK G L (A i).x) (sheen E) τ (freight E L κ (A i).x) 0 (b i) (y i)
   let u i:=Real.exp (-(echoM A i)^2); let z i:= (b i+‖w i‖)*(((p i).H.card:ℝ)* u i); have hZ: Wage A l z s:=by simpa only [zero_add] using! (hb.add hw.norm h.tense).mul ((h.dart d hd x I p).2.2.sound h|>.mul (woe h s))
   have hp:Wage A l g s:= H.mono hs; apply RateLE.of_norm_le (hp.add (he.add hZ h.tense) h.tense)
   filter_upwards [hv,h.port,hn t,hx,h.dress,h.tins t,H₀,h.high.eventually_gt_atTop 1] with i hF hi ht' he hh hk hy hG
   obtain ⟨hl,-,-⟩:= hi.port; obtain ⟨hh',hz⟩:=hh; obtain ⟨hf,hv,Hq,H⟩:=he; obtain ⟨hy,hΨ,hζ⟩:=hy
   have hA:0≤ skimX G L (A i).x := Real.rpow_nonneg (show 0≤betaF G (A i).x L from le_trans zero_le_one hG.le) _; have hV:1 ≤ echoM A i:=Delay.bill_ge ..
   let R:=(A i).R; let S:=(A i).V; let V:=(A i).sheet.V; let v':= S.push R.beta R.eval V
   have hv₀:v'>0:=hF.branch
   have hu:0≤ freight E L κ (A i).x:=by
      -- Apply the charge bound to a leaf of unit weight to obtain nonnegativity.
      let M':Leaf S R:= { turn:= .gasKey 0, ingredient:=fun _=>0, scopedR:=fun _ _ _ _=>rfl, grant:=fun _ h=> (h rfl).elim, blank:=trivial,weight:=1, earn:=fun _=>by simp,glows:=fun _ _ _=>rfl,borel:=measurable_const }
      have hv:=(norm_nonneg _).trans (hF.charge M')
      by_contra! hp; exact (not_lt.mpr hv) (by
         change freight E L κ (A i).x * v'* Real.exp _ *1 < 0; rw [mul_one]; exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hp hv₀) (Real.exp_pos _))
   let f' : Config G (A i).f→ℝ:= fun U=> f i (chant _ _ U)-w i; let g' : Config G (A i).f→ℝ := f i ∘ chant _ (I i)
   have hI : Envelope g':= Env.along hf (chant_m ..); have hb:R.eval*f'=R.eval*g'-R.eval * (fun _=>w i):=by ext x; dsimp; unfold f' g'; rw [mul_sub]; rfl
   have hP (u:ℝ): S.push R.beta (R.eval*fun _=>u) V= v'*u:=by unfold StepData.push; simp_rw [Pi.mul_apply, smul_eq_mul, ← mul_assoc, integral_mul_const]; rfl
   let H:= outline (a:=a₀ i) (B:=B i) (p i).good hl hi.budget.1 V (k i) (f i) hf hv hi.mass hF.flare hi.width hh' le_rfl 
           (fun u hu => ht' (p i).Q u hu) hk (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hV ht) hA) (mul_nonneg hA (pow_nonneg (zero_le_one.trans hV) _)) hy (by unfold sheen; linarith [E.usable,E.grants.1]) (half_pos E.usable) hζ (Real.exp_nonneg _) hΨ hF.branch.le H hF.leaves hu Hq
   have hz': ‖S.push R.beta (R.eval*f') V‖ ≤ v' * (g i+(e i+ z i)) := H
   have hs': S.push R.beta (R.eval*f') V= v' *((A i).arg (I i) (f i) - w i) := by
       let u:=fun _:Config G (A i).f=>w i; have hR:=R.envelope hi.budget.1
       rw [show (A i).arg (I i) (f i)=_ from (show (A i).arg (I i) (f i)= S.push R.beta (R.eval*g') V /v' from rfl),mul_sub]
       have hk : S.push R.beta (R.eval*f') V=S.push R.beta (R.eval*g') V-S.push R.beta (R.eval*u) V :=by
          unfold StepData.push; simp only [hb,Pi.sub_apply,smul_sub]; rw [integral_sub (StepData.push_slice (S.isKernel hl _) V (R.eval*g') ((hR.mul hI).integrable _)) (StepData.push_slice (S.isKernel hl _) V (R.eval*u) ((hR.mul (Envelope.const _)).integrable _))]
       change S.push _ _ _=_; rw [hk, hP, mul_div_cancel₀ _ hv₀.ne'] 
   apply le_of_mul_le_mul_left _ hv₀; rw [hs',norm_mul,Real.norm_of_nonneg hv₀.le] at hz'; exact hz'
end Chase
end YM.PhysicalNext.Repeat.Aroma
