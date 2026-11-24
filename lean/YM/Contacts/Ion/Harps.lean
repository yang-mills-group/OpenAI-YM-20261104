import YM.Contacts.Ion.Globe
namespace YM.Contacts.Lyre
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie Harrier Sequent
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k i r l j M D:ℕ}{ζ σ:ℝ≥0}
open UVNext PricedKernels Next.Free Lattice Tree FreeResolvent
open PertExtension.Orb MeasureTheory
namespace Align
-- symmetry on trees and relative insertion (global branch art).
set_option autoImplicit false
open MeasureTheory PertExtension.Orb
local notation "U"=> OEdge
abbrev baseMeasure (G:Gauge)(ι:Type) [Fintype ι]:=Measure.pi (fun _ :ι=>G.probHaar)
instance normHere (G:Gauge)(ι:Type)[Fintype ι]: IsProbabilityMeasure (baseMeasure G ι):= inferInstanceAs (IsProbabilityMeasure (Measure.pi _))
variable {f:Side}(S:StepData m f)(h:S.patch.Branches S.kernel G)
variable (x:Entry G f)(y:Entry G m)
def noise (b:ℝ)(V:Config G f)(Y:Config G m) : ℝ:= ∏ i: U m,S.penaltyWeight b (Y i.val*(S.prediction V (art S) i.val)⁻¹)
abbrev bells (b:ℝ) := Align.noise (G:=G) S b (liftLinks x) (liftLinks y)
lemma deliver (b:ℝ): Align.bells S x y b = Real.exp (-b *(S.kernel.penalty)*orbitC S x y):= by
   unfold bells noise StepData.penaltyWeight; rw [← Real.exp_sum,orbitC,Finset.mul_sum]; rfl
local notation "Φ" => (baseMeasure G)
lemma one_part (b:ℝ)(v:G.El): (∫ p:G.El,S.penaltyWeight b (p*v⁻¹) ∂G.probHaar)=S.penaltyZ b G:= (measurePreserving_mul_right G.probHaar v⁻¹).integral_comp ((Homeomorph.mulRight v⁻¹).measurableEmbedding) (S.penaltyWeight b)
theorem together (b:ℝ) (P:Config G f): (∫ y:Entry G m,Align.noise S b P (liftLinks y) ∂Φ (U m)) = (S.penaltyZ b G)^ (Fintype.card (U m)):= by
   let k(y:Entry G m)(i:U m):=S.penaltyWeight b (y i*(S.prediction P (art S) i.val)⁻¹); unfold Align.noise; simp_rw [lift_at]; rw [integral_fintype_prod_eq_prod (fun (i:U m) y=> S.penaltyWeight b (y*(S.prediction P (art S) i.val)⁻¹))]; simp_rw [Align.one_part S b,Finset.prod_const,card_univ]
lemma plus (b:ℝ):0<bells S x y b:= by rw [deliver]; exact Real.exp_pos _
include h
lemma measures (b:ℝ): Measurable (fun p: Entry G f × Entry G m=> bells S p.1 p.2 b):= by
    simp_rw [deliver]; apply Real.measurable_exp.comp; unfold Align.orbitC; refine Measurable.const_mul (?_) _; refine Finset.measurable_fun_sum _ (?_); intro i _; unfold dawn; apply Measurable.comp ((show Continuous G.price by fun_prop).measurable); exact ((measurable_pi_apply i.val).comp ((lift_cont G).measurable.comp measurable_snd)).mul (((measurable_pi_apply i.val).comp ((S.prediction_meas h (art S)).comp ((lift_cont G).measurable.comp measurable_fst))).inv)
lemma gauged (p:Site f→G.El) (b:ℝ)(x:Config G f)(y:Config G m):Align.noise S b (gauge p x) (gauge (p∘S.ratio.embed) y)=Align.noise S b x y:= by
   let f:= p ∘ S.ratio.embed; unfold Align.noise; rw [(Push.SectorMeasure.choice_gauge h ..).2]; refine Finset.prod_congr rfl fun i _=> ?_; let Q:=S.prediction x (art S); let j:=i.val; let v:=j.1; let a:=j.1+step j.2; unfold StepData.penaltyWeight; change Real.exp (-b*S.kernel.penalty*G.price (f v*y j*(f a)⁻¹* (f v*Q j*(f a)⁻¹)⁻¹))= Real.exp (-b*S.kernel.penalty*G.price (y j*(Q j)⁻¹)); rw [show f v*_*(f a)⁻¹ * _=f v*(y j*(Q j)⁻¹)*(f v)⁻¹ from (show f v*y j*(f a)⁻¹*(f v*Q j*(f a)⁻¹)⁻¹=_ from by group), G.price_conj]
-- scored upper bound to localize. positive exponent real.
omit h
lemma cloud (h:0≤b)(V:Config G f)(Y:Config G m):Align.noise S b V Y ≤ 1:= by
   have he : ∀ x:G.El, 0 ≤ S.penaltyWeight b x:= fun _=> (Real.exp_pos _).le
   have hq(x:G.El): S.penaltyWeight b x ≤ 1:= Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h) S.kernel.penalty_pos.le) (G.price_range x).1); apply Finset.prod_le_one; exact fun _ _=>he _; exact fun _ _=>hq _ -- name
end Align
end
end YM.Contacts.Lyre
