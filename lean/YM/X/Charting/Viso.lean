import YM.X.Charting.Crest
/-!
Exact inversion identity for integrated cubic in orbit calculation. Used TWICE in center comparison. No inference that correlations invariant under all translations on finite quotient.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Hinge
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Radial
open Source ProjectorNext.Calibration Gauss Next.Rank Normal MvPolynomial Finsupp
open Feyn Gauge LatticePT PertExtension.Orb Chart Stems PertExtension.Series.Tested Finset Interval Size Asymptotics
open Pert.Orb (positiveLinks wilson Potential)
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {n:Side} {q:ℕ+}(p : PlaqAxes)(x:Site n)
local notation "U"=> Potential G n -- issue
local notation "J"=> Jam n G

lemma flips (A:U)(i:PlaqAxes)(x:Site n): G.price (faceValue (positiveLinks A) (second i x,i)) = G.price (faceValue (positiveLinks A) (x,i)):= by -- remove j
  let a:= i.val.1; let b:=i.val.2; let y:=second i x; let u(c : Site n)(d:Axis):= positiveLinks A (c,d)
  have he (c : Site n)(d:Axis): u (-c-step d) d=(u c d)⁻¹:= by change G.lieExp (A.val (Pert.Orb.image (c,d)))=_; rw [A.property,Work.F03.exp_neg_color];rfl
  let P:=u x a*u (x+step a) b; let q:=(u (x+step b) a)⁻¹*(u x b)⁻¹
  have h: G.price (q*P)= G.price (P*q):= calc _ = G.price (q*(P*q)*q⁻¹) := congr_arg G.price (by group)
                                            _ = _ := G.price_conj ..
  simp [faceValue,Pert.Bare.square_links]; change G.price (u y a*u (y+step a) b*(u (y+step b) a)⁻¹*(u y b)⁻¹)= G.price (P*_*_)
  have ha:y= -(x+step b)-step a:=by dsimp [y,second,a,b]; abel
  have hb:y+step a= -x-step b:= by rw [ha]; abel
  have hk:y+step b= -x-step a:=by rw [ha]; abel
  have hi:y= -(x+step a)-step b:= by rw [ha]; abel
  rw [hb,hk,he x a,he x b]; conv_lhs=> rw [show u y a=(u (x+step b) a)⁻¹ from ha ▸ he (x+step b) a, show u y b=(u (x+step a) b)⁻¹ from hi ▸ he (x+step a) b, inv_inv, inv_inv]
  convert h using 2 <;> simp [P,q,u,mul_assoc,a,b]
lemma sees (A:U) : glaze A (hairAt (second p x) (vertex p))= glaze A (hairAt x (vertex p)):= by
   simp_rw [shades, Stems.vertex, mark_test]; apply congr_arg Complex.ofReal; apply congr_arg (fun f:ℝ→ℝ=> Jet.someJ f 3); funext z; exact (along_fire A (second p x,p) z).symm.trans ((flips (z • A) p x).trans (along_fire A (x,p) z))
lemma focus_eq {L R:poly J}(h:∀ A:U,glaze A L=glaze A R): mean L=mean R:= by
   rw [← sub_eq_zero, ← map_sub]; exact (sprinters 0 (L-R) (fun i=> by rw [map_sub,h,sub_self];rfl)).trans (show (fog 0:ℂ)=0 from congr_arg Complex.ofReal (Gauss.average_zero _ _)) -- type ambig
lemma faces (f:poly J): shock water (hairAt (second p x) (vertex p)*f)=shock water (hairAt x (vertex p)*f):= focus_eq fun A=>by rw [map_mul,map_mul,sees]
end YM.PositionX.Hinge
