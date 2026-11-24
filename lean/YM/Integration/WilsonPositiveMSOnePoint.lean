import YM.Integration.WilsonRichFirstConnectedFields
import YM.MS.Fleet.Place

/-! Every strictly positive homogeneous MS mark has zero independent unconnected
one-point coefficient at every coupling order. The original multileg field can be
nonzero: for its empty word the true finite clock polynomial is killed by its
engineering exponential at the actual infrared boundary. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositiveMSOnePoint
open Function Filter Set Finset MeasureTheory MS MS.Plane MS.Arts MS.Landau MS.Landau.Detect MS.Osc MS.Osc.Snap MS.Tone
open MS.Rake MS.Rake.Geo MS.Dial MS.Vane MS.Motif MS.Local.Physical MS.Land MS.Pearl MS.Outlook MS.Alps MS.Emit MS.Dock MS.Hem MS.Logarithm MS.Train
open MS.Tide
open scoped Classical Topology BigOperators
variable {G:Gauge} {B:Deck G} {A:Booked B} {W:Type} [LinearOrder W]

private theorem polynomial (p:Polynomial ℝ)(d μ:ℝ)(hd:0<d):
    Tendsto (fun t:ℝ=>p.eval (μ+t)*Real.exp (-d*t)) atTop (𝓝 0):=by
  induction p using Polynomial.induction_on' with
  | add p q hp hq=>simpa only [Polynomial.eval_add,add_mul,add_zero] using hp.add hq
  | monomial n c=>simpa only [Polynomial.eval_monomial,mul_assoc,mul_zero] using (MS.Fleet.exp_keep d hd n μ).const_mul c

private theorem regular (f:ℝ→ℂ)(hf:Ready f)(d μ:ℝ)(hd:0<d):
    Tendsto (fun t:ℝ=>(Real.exp (-d*t):ℂ)*f (μ+t)) atTop (𝓝 0):=by
  apply hf.Ind (p:=fun f=>Tendsto (fun t:ℝ=>(Real.exp (-d*t):ℂ)*f (μ+t)) atTop (𝓝 0))
  · intro p z
    have a: Tendsto (fun t:ℝ=>((p.eval (μ+t)*Real.exp (-d*t):ℝ):ℂ)) atTop (𝓝 0):=by
      simpa only [Function.comp_def,Complex.ofReal_zero] using (Complex.continuous_ofReal.tendsto _).comp (polynomial p d μ hd)
    simpa only [Complex.real_smul,Complex.ofReal_mul,mul_left_comm,mul_assoc,zero_mul] using a.mul_const z
  · simpa only [Pi.zero_apply,mul_zero] using (tendsto_const_nhds : Tendsto (fun _:ℝ=>(0:ℂ)) atTop (𝓝 0))
  · intro f g hf hg;simpa only [Pi.add_apply,mul_add,add_zero] using hf.add hg
  · intro c f h;simpa only [Pi.smul_apply,Complex.real_smul,mul_left_comm,mul_zero] using h.const_mul (c:ℂ)

private def emptyRead : MS.Arts.Mob G→ₗ[ℝ]ℂ where
  toFun f:=f 0 []
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

theorem cutoff {h:ℕ}(X:Flats G)(admitted:Host X h)(positive:0<h)(μ:ℝ):
    Tendsto (fun t:ℝ=>hereZ h X t μ 0 []) atTop (𝓝 0):=by
  obtain ⟨m,license⟩:=tallP (Moony.toast admitted.bill)
  have rent:=((press_ready (n:=m) (F:=X) m).linear (emptyRead (G:=G)))
  have boundary:=regular _ rent (h:ℝ) μ (by exact_mod_cast positive)
  apply boundary.congr' (Eventually.of_forall fun t=>?_)
  rw [vertical license admitted.tall]
  have phase:amount (-(h:ℂ)) t=(Real.exp (-(h:ℝ)*t):ℂ):=by
    simpa only [Complex.ofReal_neg,Complex.ofReal_natCast] using amount_mint (-(h:ℝ)) t
  simp only [plow,MS.Alps.mass,fieldDim,List.map_nil,List.sum_nil,Int.cast_zero,add_zero,phase,sr];rfl

theorem archived (M:MS_Data G A)(v:Label B)(hp:0<v.h)(k:ℕ)(μ:ℝ):Tendsto (fun t:ℝ=>Archive v.h (M.marks v.h v.item) k (μ,t) []) atTop (𝓝 0):=
  cutoff _ (Host.host (gang (M.markOK v.h v.item k))) hp μ

theorem row {I:Type}(P:Geo I)(M:MS_Data G A)(a:Label B)(hp:0<a.h)(k:ℕ)(i:I):
    Vane.blade (rowM P M a k) i=0:=by
  unfold Vane.blade rowM Rake.circle Rake.nameR
  have H:=archived M a hp k (P.η i)
  exact H.limUnder_eq

theorem connected (M:MS_Data G A)(p:W→Label B)(u:ℝ){x:W→QP}(sep:Injective x)(w:W)(positive:0<(p w).h)(k:ℕ):
    Dial.book M p u x {w} k=0:=by
  change Vane.blade (spine M p u x {w} k) ()=0
  rw [(pin M p u sep).2.1 w];exact row (frameF Unit u) M (p w) positive k ()

end YM.Integration.WilsonPositiveMSOnePoint
