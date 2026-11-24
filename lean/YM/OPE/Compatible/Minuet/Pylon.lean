import YM.OPE.Compatible.Minuet.Chips
/-!
 # Escape from exterior by uniform estimate; film powers. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open AnalyticBridge.VerifiedReset
open Next.Rank.Thirst
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P':Teller G} {T: Tube G S} {R : Rep G f}
    {p : BudgetPoint} {m n: ℕ} {W a r t σ E Λ μ x κ C w ε D b B: ℝ}
variable {F:Forest S.ratio} {I J:Seats F}{X Y Z:Support f}{q:Support c}
variable (H:Primacy F I J Y X Z q R.p.B n) (P: S.patch.Branches S.kernel G)(hR:R.Lawful σ C Λ E w)(V:Config G c)(k:S.Choices)
variable (f':World F I G→ℝ)(hf:Envelope f'){A:ℝ}(hw:∀ w,‖f' w‖≤A)
local notation "fL"=> allege I J R V m k a B H.nested f'
def slipF (F:Forest S.ratio)(J:Seats F)(a:ℝ)(U:Config G f):= ∑ j∈J, film F j U a
lemma lantern (F:Forest S.ratio)(J:Seats F)(a:ℝ)(U:Config G f): 0 ≤ slipF F J a U:= Finset.sum_nonneg fun i _=>by unfold film; split <;> norm_num
lemma author (F:Forest S.ratio)(J:Seats F) {I} (hp:I ⊆ J) (U:Config G f) (h:¬ dazed hp a B (chant F J U))(hb:a ≤ B): 1 ≤ slipF F J a U:=by
    have ht:∃ i∈J,a<G.chord (pantone F U i.val):=by
       by_contra! hh; exact h ⟨fun i=> (hh _ (hp i.property)).trans hb, fun i _ => hh _ i.property⟩
    obtain ⟨i,hi,h⟩:=ht
    rw [show 1=(fun j=> film F j U a) i from (if_pos h).symm]; exact Finset.single_le_sum (s:=J) (fun i _=> show 0 ≤ film F i U a from by unfold film;split <;> norm_num) hi
section count
variable (hC:∀ U,0≤R.eval U){ℓ:ℝ} (hb:∀ j:F.Free, ‖S.push R.beta (fun U=>R.eval U*film F j U a) V‖≤S.push R.beta R.eval V * ℓ)
local notation "c'"=> S.push R.beta R.eval V
include P hR hC hb
lemma contrast {g:Config G f→ℝ}{ε t:ℝ}(hg:Envelope g)(_he:0 ≤ ε)(ht:0 ≤ t)(hv:∀ U, ‖g U‖ ≤ ε + t*slipF F J a U):
 ‖S.push R.beta (R.eval*g) V‖ ≤ c' * (ε+t*(J.card*ℓ)) := by
   let η:=prior G f;let u x:=S.density R.beta x V * R.eval x; let e i (x:Config G f):=film F i x a
   have hK:=S.isKernel P R.beta; have hi x:0≤u x:=mul_nonneg (hK.positive x V) (hC _); have hI : Integrable u η:=StepData.push_slice hK V R.eval ((R.envelope hR).integrable _)
   have hj (g:Config G f→ℝ)(hp:Envelope g): Integrable (fun x=> u x*g x) η := by
       simp_rw [u, mul_assoc]; exact StepData.push_slice hK V _ (((R.envelope hR).mul hp).integrable _)
   have hx(i:F.Free):Envelope (e i):=(movie (R:=R) F i a).env
   let φ (x:Config G f):= slipF F J a x
   have hh: Integrable (fun x=>u x*φ x) η:=by unfold φ slipF; simp_rw [Finset.mul_sum]; exact integrable_finsetSum _ fun i _=>hj _ (hx i)
   have hz: ∫ x,u x*φ x ∂η ≤ J.card*(c'*ℓ):=by
       unfold φ slipF; simp_rw [Finset.mul_sum];rw [integral_finsetSum];swap; · intro i _;exact hj _ (hx i)
       rw [show (J.card:ℝ)*(c'*ℓ)=∑ _i∈J,c'*ℓ from by simp]; refine sum_le_sum fun i _=> ?_; unfold u; simp_rw [mul_assoc]; exact (Real.le_norm_self _).trans (hb i)
   have h₁: S.push R.beta (R.eval*g) V=∫ x,u x * g x ∂η:=by unfold u StepData.push; simp_rw [smul_eq_mul,mul_assoc,Pi.mul_apply]; rfl
   have h₂ : (∫ x,u x ∂η)=c':=rfl
   rw [h₁]; apply (norm_integral_le_integral_norm _).trans; apply le_trans (b:=∫ x,(u x*ε+t*(u x*φ x)) ∂η) (integral_mono ?_ ((hI.mul_const ε).add (hh.const_mul t)) (fun U=>?_))
   · rw [integral_add (hI.mul_const _) (hh.const_mul _),integral_mul_const,integral_const_mul,h₂]; apply (add_le_add le_rfl (mul_le_mul_of_nonneg_left hz ht)).trans_eq; ring
   · unfold u; simp_rw [mul_assoc]; exact StepData.push_slice hK V _ (((R.envelope hR).mul hg).integrable _)|>.norm
   rw [norm_mul,Real.norm_of_nonneg (hi _)]; exact (mul_le_mul_of_nonneg_left (hv _) (hi _)).trans_eq (by unfold φ; ring)
variable (hD:WilsonStartup.Decent R.clip R.p)(hy:Geo.Width R.p R.clip σ)(hk:m ≤ R.p.B)(hN:∀ U:Config G f,naked S q n U B→ ordFrame S (halo 1 q) U ∧ ordBest S q U)(hβ:4*B≤ R.p.threshold)(ha:a ≤ B)(hv:0≤B)
-- fee formula.
def promotion (R:Rep G f) (m:ℕ)(X:Support f) (w t e r k A x:ℝ):= A*2*(2*x+ Real.exp ((t+e)*coverNumber R.p.B X)*(4*Shade R*w/e)*r*Real.exp x)+k*0+(m:ℝ)*0
include H hR hD hy hk hN hβ ha hv hf hw
lemma outline (hc:Sable R S X (r+t) (cinnamon R m I) x) (he:0≤r)(hj:0<t) (hy':x≤1) (hx:0 ≤ w)(hθ:4 * Shade R * w ≤ t)(hZ:0≤ c') {u K:ℝ}(ho:∀ y:World F J G,dazed H.nested a B y→ ‖report I J R V m k B f' y-u‖≤ ε) (hK : Besotted R S r K V w)(hP:0≤K)(hδ:0 ≤ ε):
    ‖S.push R.beta (R.eval*(fun U=>f' (chant F I U)-u)) V‖ ≤ c' * (promotion R m X w r t K 0 A x+(ε + (A+‖u‖)*(J.card*ℓ))) := by
    let g(U:Config G f):= f' (chant F I U)-u; let v:= fL
    have hp: Paced R X S v (2*A):= allegation H P hR V k f' hf hw; have hs: Envelope (g-v):=by
       have h:Envelope g:= by unfold g;simp_rw [sub_eq_add_neg]; exact (Env.along hf (chant_m F I)).add ((Envelope.const u).neg)
       rw [sub_eq_add_neg]; exact h.add hp.env.neg
    have ha' := paint hR (S.isKernel P _) hC he hK hP hZ H.broad.present hx hj hθ hc hy' hp (chips H P hR V k f' hf hw hD hy hk hN hβ ha hv (add_nonneg he hj.le) hc)
    have hg: 0≤ A:=(norm_nonneg _).trans (hw 1)
    have ht:∀ U, ‖(g-v) U‖≤ ε+(A+‖u‖)*slipF F J a U:=by
       intro U; let σ:= chant F J U; by_cases h:dazed H.nested a B σ
       · rw [Pi.sub_apply]; unfold g v allege trawl; dsimp only [Function.comp_apply]; rw [if_pos h]; let s:= report I J R V m k B f' σ
         change ‖f' (chant F I U)-u-(f' (chant F I U)-s)‖≤_
         rw [show f' (chant F I U)-u-(f' _-s)=s-u by ring]; apply le_trans (ho _ h) (le_add_of_nonneg_right (mul_nonneg (add_nonneg hg (norm_nonneg _)) (lantern ..)))
       rw [Pi.sub_apply, show v U=0 from if_neg h,sub_zero]; exact (norm_sub_le ..).trans ((add_le_add (hw _) le_rfl).trans ((le_mul_of_one_le_right (by positivity) (author F J H.nested _ h ha)).trans (le_add_of_nonneg_left hδ)))
    rw [show R.eval*g=R.eval*(g-v)+R.eval*v from by ring, StepData.push_add (S.isKernel P R.beta) (R.eval*(g-v)) (R.eval*v) (((R.envelope hR).mul hs).integrable _) (((R.envelope hR).mul hp.env).integrable _),Pi.add_apply]
    apply (norm_add_le ..).trans; exact (add_le_add (contrast P hR V hC hb hs hδ (by positivity) ht) ha').trans_eq (by unfold promotion; ring)
end count
end YM.PhysicalNext.Repeat.Aroma
