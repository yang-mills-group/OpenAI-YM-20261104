import YM.OPE.Compatible.Arch.Vessel
/-!
# Position comparability. Equality of vacuum jets suffices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision
variable {I J:Type}{G:Gauge}[Fintype I][Fintype J]
open Radial Zone ScriptJ Metric
local notation "W" => Chart.tangent G I
local notation "Lf" => Tested.germ
variable {P:ChartRatio G}
lemma sameCap {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{A:ℝ→ E→ℝ}{p:ScriptJ E}(h:Pawn A)(hv:∀ x,Reads (fun t=>A t x) (p x)): Cape A p:=by obtain ⟨a,ha⟩:=h; have he:a=p:=funext fun x=> (ha.stale x).equality (hv x); exact he ▸ ha
lemma labQuitt {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]{p:ScriptJ E}(h:p.B)(t:ℝ): Measurable fun i:E=>(p i).atK t:=
     ((bondX h).1.smooth.continuous.measurable.add (((bondX h).2.1.smooth.continuous.measurable).const_mul t)).add (((bondX h).2.2.smooth.continuous.measurable).const_mul _)
namespace Dimes
variable (A:Dimes G I J)
/-- covenant. Series via rescaled path -/
structure Globe (K:Lid G I)(L:Lid G J): Prop where
    pledge : Cel (L.f ∘ A.gradient)
    signs : Stationary (L.f∘A.gradient)
    mark : Pawn.mold K.f 2= Pawn.mold (L.f ∘ A.gradient) 2
    mold : Pawn.mold K.w 0=Pawn.mold (L.w ∘ A.gradient) 0
-- from input equality path Ward
structure Mint (K:Lid G I)(L:Lid G J): Prop where
    earns (x:Keys G I): Reads (fun t:ℝ=> L.f (A.gradient (t • x))/t^2) (Pawn.mold K.f 2 x)
    commits (x:Keys G I): Reads (fun t:ℝ=> L.w (A.gradient (t • x))) (Pawn.mold K.w 0 x)
-- stationary under comp from bore gradient zero
lemma chore (L:Lid G J): Stationary (L.f ∘ A.gradient):=by
     have hv : ContDiffAt ℝ ∞ (L.f∘A.gradient) 0:=(show ContDiffAt ℝ ∞ L.f (A.gradient 0) from by rw [grad0]; exact L.F.smooth).comp _ A.gradC
     have hh : fderiv ℝ (L.f∘ A.gradient) 0=0:=by
       have he : fderiv ℝ L.f 0=0:=by ext x; have hp:= L.F.base1 x; unfold jet at hp; simpa only [iteratedFDeriv_one_apply, Nat.factorial_one, Nat.cast_one, inv_one, one_mul, _root_.zero_apply] using hp -- name
       rw [fderiv_comp,grad0,he]; rfl -- simpl
       · rw [grad0]; exact L.F.smooth.differentiableAt (by simp)
       exact A.gradC.differentiableAt (by simp)
     exact ⟨hv,by rw [Function.comp_apply,grad0,L.F.base0],fun u=> by unfold jet; rw [iteratedFDeriv_one_apply,hh];simp⟩
namespace Mint
variable {A}{K:Lid G I}{L:Lid G J}
lemma borders (D:Mint A K L) : Globe A K L :=by
    have he := A.chore L; have hx: Pawn.mold K.f 2=Pawn.mold (L.f ∘ A.gradient) 2:=funext fun x=> (D.earns x).equality ((Pawn.trio he).stale x)
    refine ⟨?_,he,hx,?_⟩
    · obtain ⟨c,hc,h⟩:= K.bright; exact ⟨c,hc,fun x=> (h x).trans_eq (congr_arg JetS.s (congr_fun hx x))⟩
    have ht : ContDiffAt ℝ ∞ (L.w∘A.gradient) 0:=(show ContDiffAt ℝ ∞ L.w (A.gradient 0) from by rw [grad0]; exact L.coat).comp _ A.gradC
    exact funext fun x=> (D.commits x).equality ((Pawn.calm ht).stale x)
end Mint
def pulse (p:ScriptJ (Keys G I))(q:ScriptJ (Keys G J)):=∀ x,Reads (fun t:ℝ=> (q (t⁻¹ • A.gradient (t•x))).atK t) (p x)
lemma congr_charge {K:Lid G I}{L:Lid G J}(h:Globe A K L){p:ScriptJ (Keys G I)}{q:ScriptJ (Keys G J)}(hp:q.B)(hv:A.pulse p q)(R:LocalRatio P): K.pay P p=L.pay P q:= by
     let f:= L.f∘ A.gradient; let w:= L.w ∘ A.gradient; let k:=K
     have h0:0<w 0:=by unfold w; rw [comp_apply,grad0]; exact L.charm
     have hf: ContDiffAt ℝ ∞ w 0:=(show ContDiffAt ℝ ∞ L.w (A.gradient 0) from by rw [grad0]; exact L.coat).comp _ A.gradC
     let C:Lid G I:=⟨f,h.signs,L.fmeas.comp A.meas_grad,h.pledge,w,h0,hf,L.gleams.comp A.meas_grad⟩
     have he: ∀ y t,L.mode t (A.q (put y))=C.w y*Real.exp (-C.f y/t^2):=fun _ _=>rfl
     let F(t:ℝ)(x: Tile G J):= (q (t⁻¹ • intake G J x)).atK t*L.mode t x
     have hF (t):Measurable (F t) := ((labQuitt hp t).comp ((measurable_const_smul t⁻¹).comp introM)).mul (L.meas t)
     have hx(t:ℝ):Measurable fun i:Tile G I=>F t (A.q i):=(hF _).comp A.q.measurable
     have ht(t:ℝ):Measurable fun i:Tile G I=> L.mode t (A.q i):= (L.meas _).comp A.q.measurable
     have ha: Snap (fun t i=>F t (A.q i)) (C.capstone P p):= C.reading P R (sameCap (Pawn.amplified _ A.gradC A.grad0 _ hp) hv) (fun t=> (labQuitt hp t).comp ((measurable_const_smul t⁻¹).comp (A.meas_grad.comp (measurable_const_smul t)))) hx (Eventually.of_forall fun y x t ht hz=> by unfold F; rw [he,hz];rfl)
     have hs: Snap F (L.capstone P q):= L.reading P R (Bears.grade hp (fun _=>le_rfl)) (labQuitt hp) hF (by filter_upwards [local_intro] with y hy x t ht hz; unfold F Lid.mode quitt; rw [hy,←hz,inv_smul_smul₀ ht.ne'])
     have hy: C.pay P p=L.pay P q:= A.covered hF L.meas ha (C.reaches1 P R ht (Eventually.of_forall he)) hs (L.foundation P R) (C.warmth P R).ne' (L.warmth P R).ne'
     rw [← hy]
     have hW: Pawn.mold (warmer P K.w) 0=Pawn.mold (warmer P C.w) 0:=by
          funext x; let M:=Pawn.mold (Chart.jacobian P (U:=I)) 0 x; have hM:Reads (fun t=> Chart.jacobian P (t•x)) M:= ((Pawn.calm ((Chart.Ratio.jacobian_smooth R).of_le le_top))|>.stale x)
          have h(K:Lid G I): (Pawn.mold (warmer P K.w) 0 x)= (Pawn.mold K.w 0 x)*M:= ((Pawn.calm (K.winds P R)).stale x).equality (((Pawn.calm K.coat).stale x).pile hM)
          rw [h K,h C,show Pawn.mold K.w 0= _ from ‹Globe ..›.mold]
     unfold Lid.pay Lid.purse Lid.capstone Lid.heat; rw [hW, show Pawn.mold K.f 2=Pawn.mold C.f 2 from h.mark,show kernel K.f=kernel C.f from funext fun x=>congr_arg (fun v:JetS ℝ=>Real.exp (-v.s)) (congr_fun h.mark x)]
end Dimes
end YM.OPE.Libra
