import YM.FVA2.StratParity
/-!
# real profiles and points. Reality for all MS arrays matching this prescription.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Plot
open Function Filter Set MS MS.Land MS.Landau MS.Logarithm MS.High MS.Tide MS.Menus
open Pert Maxwell Maxwell.Free Pert.Position Pert.RawLabels PositionX PositionX.Bend PositionX.Jet MS.Book MS.Book.Program
open Panel ColorCode Pic Forge BoxOffice WorldJet Elegant MS.Book.Convolve MeasureTheory Verne
open scoped BigOperators Classical Topology ContDiff
variable {G:Gauge}(V: Warehouse G){h:G.Simple}{B: Booked (wings G)}(M:MS_Data G B){p:ℝ}(R:Booth p V.F){s:ℝ}{n m d:ℕ}
variable (P:Land.Prescription (wings G))(HS: Blaze.ExactSpin V P)(HU:Frost.Trusted P) (H: MixedStory.AllProfiles M V P)
local notation "ℓ"=> V.F
section
variable {F:Labels.Frames G} {K:Panel F}
lemma House_sum {I:Type*}{u:I→Bank F d}(a:Finset I)(h:∀ i∈a,House (u i)): House (∑ i∈a,u i):= by induction a using Finset.induction_on with| empty=> rw [Finset.sum_empty]; exact Hcollect| insert i u hi hv=> rw [Finset.sum_insert hi ]; exact Hplus _ _ ( h i (by simp)) (hv (fun i hz=>h _ (Finset.mem_insert_of_mem hz)))
lemma hover (f:Word ℝ) (w:Word (Bank F d))(h:∀ i, House (w i)) : House (ren f w n):= by unfold Jet.ren; exact Hscale _ (House_sum _ (fun i _=> Hscale _ ( Hscale _ (h _) _) _)) _
abbrev Ereal (x:E F d): Prop:= ( Model F ).conj (hierarchy F).spin _ x=x
abbrev Aspect (P:Panel F) : Prop:= ∀ d i,House ( P.lives d i )
lemma ash (T:Strat F)(h:Aspect K)(hc:K.clearP): Aspect ( Panel.flip K T ):= by intro d i; rw [ Panel.turn_book _ _ hc ]; exact θhouse _ ( h d ) _
lemma folk (f:Word ℝ)(h:Aspect K)(hc:K.clearP): Aspect (Panel.join K f):= by intro d i; rw [ Panel.total_book _ _ hc ]; exact hover _ _ (h d)
-- fetch continuous test proof (test used no nu contact).
lemma shine (x:Points n→ℂ)(hx:ContinuousOn x ( conf n ))(h:∀ t:Test n, RealT t→ moral (t.applyTo x))(v:Polyp n) : moral (x v.val):= by
   let z(q:Points n):= star ( x q ); let K:= z-x; have he := (conf_open n).ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ:=volume) ((ContinuousOn.sub hx.star hx).locallyIntegrableOn ( conf_open n ).measurableSet) (fun g hg hg' hG=>?_); swap
   · let F : Points n→ℂ:= Complex.ofRealCLM ∘ g; have hu : tsupport F=tsupport g:= by unfold tsupport; rw [show Function.support F=Function.support g from by ext; simp [F]]
     let p:Test n:= ⟨ F,Complex.ofRealCLM.contDiff.comp hg, by rw [HasCompactSupport,hu]; exact hg',hu ▸ hG ⟩; obtain ht:= h p (fun i=> by unfold moral; exact Complex.conj_ofReal _ -- bad star R instance? ofReal
                                     );
     change ∫ x', g x' • ( z x'- x x')= (0:ℂ);
     have hQ : p.applyTo K=0:= by unfold Test.applyTo; simp_rw [ show ∀ v, K v = ( star ( x v ) - x v ) from fun _=>rfl, mul_sub ]; rw [integral_sub (p.smearing hx.star) (p.smearing hx) ]; simp_rw [show ∀ v,p v*star (x v)=star ( p v*x v ) from (fun _=> by rw [star_mul',show star ( p _ )= p _ from Complex.conj_ofReal _ ]) ]; rw [show (∫ x_1,star (p x_1*x x_1))= _ from integral_conj ]; exact sub_eq_zero.mpr ht
     rw [ ← hQ ]; apply integral_congr_ae; exact Eventually.of_forall fun i=> Complex.real_smul -- defeq
   apply sub_eq_zero.mp (show K v.val=0 from ?_); exact Measure.eqOn_open_of_ae_eq (( ae_restrict_iff' (conf_open _).measurableSet ).mpr he) (conf_open _) ( ContinuousOn.sub hx.star hx ) continuousOn_const v.property -- proof_filter
lemma report_house (he:Aspect K)(hc:K.clearP)(x:Polyp n)(v:Fin n→ E F d)(h:∀i,Ereal (v i)) : moral ( K.out d x m v ):= by
    have he : ∀ p:Test n, RealT p→ moral (p.applyTo (fun x=> K.off d x m v)):= by intro p hQ; rw [ ← Panel.newly K p v m hc ]; exact he d m p hQ v h
    rw [ ← Panel.sees _ x.property ]; exact shine _ ( hc d n m v ) he x -- maybe direction
end
local notation "Ω"=> marked V M s
include HS HU H
lemma Real_v : Aspect Ω := by
    intro d i n t hT f he; rw [Pic.payMark ]; let v:Pert.Position.Section ℓ d:= ⟨n,f,t⟩; let L:= lookie V.F v; let q:ℕ+:=3; let Z(i d:ℕ):= Elegant.unglue V P HS HU q s i d; let K:= Spring.ms V M s d; let F:=fun j=> L ( Z j d i ); have hq(j:ℕ):star (F j)= F j:= θhouse (ren (clockM P q s j) ( Elegant.motion V q j d )) ( fun i=> hover _ _ ( venue ( warehouse V ) d j ) ) (dawnFrame V P HS HU q s j d) t hT f he
    have hp:= Elegant.started V P M HS HU H q (show 1<q.val from by decide) s d i v; exact tendsto_nhds_unique ( hp.star ) ( hp.congr fun t=>( hq t ).symm ) -- orientation
include h
lemma clarity_s (S:Pic.pass V h M R): Aspect (Pic.X V h M s R) ∧ Aspect (Check V M R s S):= by
    let N:= Pic.marked V M s; have hV : Aspect ( Pic.X V h M s R ):= folk _ ( ash ( Pic.L V M s h ) ( Real_v V M P HS HU H ) ( clearMark V M s ) ) ( Panel.night _ _ ( clearMark V M s ) ); exact ⟨ hV, ash _ hV ( Pic.innerX V M s R|>.1 ) ⟩
end YM.FVA2.Plot
