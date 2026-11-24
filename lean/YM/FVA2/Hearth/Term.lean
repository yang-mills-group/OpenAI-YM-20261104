import YM.FVA2.Hearth.Rail
/-!
 # Clock valuation and branch consistency 

 An announced finite through-order is enough to compute all Open facts, using the
 same tag convention. No spanned-cost estimates here. Also prove independence when
 changing Choice on already enrolled predictor (at germ, no assertion on actual
 pre-cut physical problem with hard branches).
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Hearth
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Set MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade RGComparison.Core16 PowerSeries
open scoped Classical Topology BigOperators ContDiff
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F]
variable {n:ℕ}
lemma chip_through [FiniteDimensional ℝ E] {w z:PowerSeries ℝ}(h:Through n w z)(p:E→ℝ)(hP:Stationary p): Through n (chip w p) (chip z p):= by
 have he(x:E):Through n (Stack.read x (chip w p)) (Stack.read x (chip z p)):= by simp_rw [chip,exponent]; exact enough_c _ (costThrough h hP x)
 intro i hi; apply Subtype.ext; ext1 x; rw [←Stack.reading_term,←Stack.reading_term, he x i hi]
lemma boost_through (d:F→ₗ[ℝ] E){v w:Ticket E}(h:Through n v w): Through n (boost d v) (boost d w):= fun i hi=> by unfold boost; rw [PowerSeries.coeff_map,PowerSeries.coeff_map,h i hi]
section
variable [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]
variable (Λ Λ':Quadratic (E×F))(μ:Measure E)[μ.IsAddHaarMeasure](q:(core Λ).RespectsPrice)(q':(core Λ').RespectsPrice)
private lemma fitThrough {Q Q' W W':Ticket (E×F)}(hl:Through n Q Q')(hw:Through n W W')(h:Λ=Λ')(u:incline W)(u':incline W') : Through n (fit Λ μ q Q W) (fit Λ' μ q' Q' W'):= by subst Λ'; unfold fit uptake; exact (Through.mul (keepsThrough _ (hw.mul hl)) (Through.invAlready (keepsThrough _ hw) (spend_it (Quadratic.upright Λ μ q u)) (spend_it (Quadratic.upright Λ μ q u'))))
private lemma fitEqual (p w:Ticket (E×F)) (h:Λ=Λ') : fit Λ μ q p w= fit Λ' μ q' p w:= by subst Λ'; rfl
end
section
variable {c f:Side}{G:Gauge}{T:StepData c f}
variable (h:T.patch.Branches T.kernel G)
variable (t t':T.Choices) (P:Inside T.ratio)
include h
lemma true_sub : substep P t=ᶠ[𝓝 0] substep (G:=G) P t':= by
 let X:= Cross (G:=G) T P × Flats G c
 let k : X→ LinkFrame G f:= expLinks G _ ∘ blankRight P
 have hk : Continuous k:= continuous_pi (fun i=>G.lieExp_cont.comp ((continuous_apply i).comp (blankRight P).continuous_of_finiteDimensional))
 have hp:k 0=1:= by unfold k; rw [comp_apply,map_zero,Inherit.identity_zero]
 filter_upwards [hp ▸ (hk.tendsto 0) |>.eventually (same_choice (G:=G) T h t)] with x hx -- expression
 change distance T ((expLinks G _ x.2)*(atStep T t (k x))⁻¹)=distance T ((expLinks G _ x.2)*(atStep T t' (k x))⁻¹); unfold atStep; rw [hx t']
omit h
variable {U V: Unmasked G f} (hu:U.Q=V.Q)
variable {w z:PowerSeries ℝ} (H:Through n w z)
local notation "Q"=> gated P U t w
local notation "Q'"=> gated P V t' z

lemma quads {a b:Quadratic E}(h:a.P=b.P): a=b:= by rcases a with ⟨p,hp⟩; rcases b with ⟨q,hq⟩; congr
include h hu H
lemma acquainted : Q = Q':= by
 unfold gated; rw [hu];
 refine congr_arg (addOn (drag _ V.Q)) ?_; apply quads; apply records; intro x; rw [Quadratic.native,Quadratic.native,Laplace.jet_germ (true_sub h t t' P),show term w 0=term z 0 from H 0 (Nat.zero_le _)]
variable (q:(core (gated P U t w)).RespectsPrice)(q':(core (gated P V t' z)).RespectsPrice)
lemma holdPrice (J:ChartRatio G) : (Update P t J w U q).Q=(Update P t' J z V q').Q:= by change reduced Q q= reduced Q' q'; congr 1; exact acquainted h t t' P hu H
local notation "ξ"=> tangent G (Blocking.Index T P)
omit hu
lemma consonance (J:ChartRatio G)(hw:Through n U.W V.W) : Through n (receipt P t J w U) (receipt P t' J z V) := by
 unfold receipt; refine ((boost_through _ hw).mul (Through.refl _)).mul ?_
 have e:Stack.rise (substep (G:=G) P t)=Stack.rise (substep P t'):= Laplace.dreaming _ (true_sub h t t' P)
 refine Through.trans (chip_through H _ (subStill P t h)) ?_; simp only [chip,pay,advancing,e]; exact Through.refl _
include hu
lemma syncWeight (J:ChartRatio G)(hw:Through n U.W V.W) : Through n (Update P t J w U q).W (Update P t' J z V q').W:= by
 have hp:= acquainted h t t' P hu H; unfold Update; rw [show uptake Q' ξ q'= uptake Q ξ q from ?_]; exact keepsThrough _ (consonance h t t' P H J hw)
 congr 1; exact hp.symm
lemma syncPay (u:incline U.W)(v:incline V.W)(hw:Through n U.W V.W){J:ChartRatio G}(hi:LocalRatio J){A B:Ticket (Flats G f)}(hh:Through n A B): Through n (Broadcast P t J w U q (boost (blankRight P) A)) (Broadcast P t' J z V q' (boost (blankRight P) B)) := fitThrough Q Q' ξ q q' (boost_through _ hh) (consonance h t t' P H J hw) (acquainted h t t' P hu H) (OpenSlots.along hi w u) (OpenSlots.along hi z v)
end

section Orders
variable {G:Gauge}{J:ChartRatio G}
-- all step energies/genuine roles explicitly compatible
structure Profile {n:Side}(k:ℕ) (x y:Unmasked G n × Ticket (Flats G n)) : Prop where
 Q : x.1.Q=y.1.Q
 W : Through k x.1.W y.1.W
 F : Through k x.2 y.2

lemma logBooks {n:Side}{L:Fabric G n} {T:Cloth L}{U V:Unmasked G n}{z w:L.Cost→PowerSeries ℝ}(h:Commission J T U z)(h':Commission J T V w){A B:Ticket (Flats G n)}{p:ℕ}(he:Profile p (U,A) (V,B))(hw:∀i,Through p (z i) (w i))(u:incline U.W)(v:incline V.W)(hj:LocalRatio J): Profile p (drive T z U A J h) (drive T w V B J h'):= by
 cases T with
 | floor=> unfold drive; exact he
 | @inLayer c f S H t hf L P C=>
    rw [drive,drive]; let p:= Exists.choose h; let p' := Exists.choose h';
    exact logBooks (Exists.choose_spec h) (Exists.choose_spec h') ⟨holdPrice H t t P he.Q (hw none) p p' J,syncWeight H t t P he.Q (hw none) p p' J he.W,syncPay H t t P he.Q (hw none) p p' u v he.W hj he.F⟩ (fun i=>hw _) (funded hj (z none) u _) (funded hj (w none) v _) hj
termination_by structural T
lemma echoes {n: Side}{L:Fabric G n} (T:Cloth L) {p:ℕ} (z w:L.Accounts→PowerSeries ℝ)(Hz:∀i,0<term (z i) 0)(Hw:∀i,0<term (w i) 0)(h:∀i,Through p (z i) (w i)) {A B:Ticket (Flats G n)}(he:Through p A B) (hj:LocalRatio J) : Profile p
 (drive T (z∘some) (headquarters z) A J (collared T z hj Hz)) (drive T (w∘some) (headquarters w) B J (collared T w hj Hw)) := by
 refine logBooks (collared T z hj Hz) (collared T w hj Hw) ⟨?_,chip_through (h none) _ first_held,he⟩ (fun i=> h _) (OpenSlots.restores ..) (OpenSlots.restores ..) hj
 exact quads (congr_arg (· • MultiGauge.Splice.polar firstBill) (h none 0 (Nat.zero_le _)))
end Orders
end YM.FVA2.Hearth
