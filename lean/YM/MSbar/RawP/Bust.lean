import YM.MSbar.RawP.Flank
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.RawP
open Function Filter Whisk Lis Measuring Cacao Aqua Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side} {a b C Z B w K r:ℝ}{p k:ℕ}
open Metric Pressure AnalyticBridge.SectorAffine.Offset
local notation "W₀"=>Positions (Primary n G)
local notation "ℓ"=>Measuring.chart n G
variable {L T δ Z:ℝ}(u:ℝ){Y:Set (Positions (Primary n G))}{A:Rep G n}{F:Positions (Primary n G)→ ℝ}{l:Clip}{P:PathData G}{v:Positions (Primary n G)}
-- space wires Roil orientation unnormalized.StepR.Data.Material. uniform enough using α0=w^-2 bought ∃ E fixed if a lower∈[σ/2,σ]. Monotonize law σ and use Wind increase? h required a≤σ−... ; choose a variable? B paid at σ/2 and wind holds for higher a.
structure Brass (G:Gauge)(l:Clip)(σ C b:ℝ)(p:ℕ)(u K Z B:ℝ):Prop where
    a0:0<b
    plank : PaintSupply G p K
    crane : σ=u+2*(3*b)*p
    unit_ : Wind G u Z p
    bin : ∀ v:G.Color, ‖v‖≤ Z*C → Allows p coinP v B
variable (σ:ℝ)(h: Brass G l σ C b p a K Z B) (hZ:A.clip=l) (hl:A.Lawful σ C L T δ)
noncomputable def bust (p:ℕ)(G:Gauge)(l:Clip)(P:BudgetPoint)(b β K C Z B L T:ℝ) := |β| *(kernelCost G l C K Z b B p + pulp Z b C p 3+pulp Z b C p 4) +pulp Z b L p 2+cork G P p b*(T*countCost b)
variable (hm: Convex ℝ Y)(hx:v∈Y)(ho:IsOpen Y)(ht:Bash Y A.p)(hg:p ≤ A.p.order)(he:‖v‖<1)(hw:3*b*p*(4*A.p.B+2:ℕ)≤A.p.supportExponent)
include h hZ hl hg hm hx ho ht he hw
lemma residence : Roil (walnut A) p b v (bust p G l A.p b A.beta K C Z B L T):=by
    subst l; rcases hl with ⟨hL,hA⟩; rw [h.crane] at hL; let R:=collectT n A.path A.clip; let V:= liveLoop n A.path; let B' := arc A.activities A.p
    have hv:= hullC A.path A.clip hL h.plank h.unit_ he h.a0 B h.bin; have hu:= loopC A.path A.clip hL h.unit_ he h.a0; have hs:=arcs hA ho ht hm v hx hg h.a0 hw
    let g:= Function.const (Positions (Primary n G)) (A.v*(Fintype.card (Site n):ℝ)); let f'(x:Positions (Primary n G)):=g x+ (-1:ℝ)*((A.beta*R x+V x)+B' x); have hp: walnut A=ᶠ[𝓝 v] f':=by
        filter_upwards [(show ∀ᶠ a in 𝓝 v,a∈Y from ho.mem_nhds hx)] with x hx; have hl: A.Lawful σ C L T δ:=⟨h.crane.symm ▸ hL,hA⟩; apply (pie A hl ht x hx).trans; change g x-(A.beta*R x+V x)-B' x=f' x; unfold f'; ring
    let Q:=bust p G A.clip A.p b A.beta K C Z B L T; have he:Roil f' p b v Q:= Roil.mono (Roil.plus (Roil.still (A.v*↑(Fintype.card (Site n)))) (Roil.scale ((hv.scale A.beta).plus hu|>.plus hs) (-1))) (by unfold Q bust;simp)
    exact ⟨he.1.congr_of_eventuallyEq hp,he.camp,fun i L hl=> le_trans (le_of_eq (congr_arg abs (Lis.follows _ hp|>.eq_of_nhds))) (he.wallet i L hl)⟩
omit h hZ hl hg hm hx ho ht he hw
lemma tempoP (r:ℝ)(hx : Roil F p b (r • v) C)(he:|r| ≤1): Roil (fun y=> F (r • y)) p b v C:=by
    let f := r • ContinuousLinearMap.id ℝ W₀; have h:ContDiffAt ℝ p F (f v):=hx.1; refine ⟨h.comp v (f.contDiff.contDiffAt),hx.2,fun i L hh=>?_ ⟩; let z:= List.map (@bolt (Primary n G)) (i::L); have hm:z.length≤ p:=by unfold z; rw [List.length_map,List.length_cons]; omega
    change |roc (F ∘ f) z v| ≤ _; rw [toe f p z h hm]; have hV:z.length=(List.map (fun i=>f i) z).length:= (List.length_map _).symm
    suffices hh':|roc F (List.map f z) (f v)|≤ |roc F z (f v)| from hh'.trans (hx.wallet _ _ hh)
    have he'(z: List (Positions (Primary n G)))(k:z.length≤p): roc F (List.map f z) (f v)=r^z.length *roc F z (f v):=by
         have hV(k z)(k':(z:List (Positions (Primary n G))).length≤k)(p':Positions (Primary n G))(hk:ContDiffAt ℝ k F p'): roc F (List.map f z) p'=r^z.length*roc F z p':=by
             induction z generalizing p' with
             | nil=> simp
             | cons a z ih=>
                have he:z.length<k:=by simp only [List.length_cons] at k'; omega
                have hz: roc F (z.map f)=ᶠ[𝓝 p'] (fun y=>r^z.length*roc F z y):= (hk.eventually (by simp)).mono (fun i h=> ih he.le i h); rw [List.map_cons, roc, hz.fderiv_eq, roc,List.length_cons, fderiv_const_mul]; change (r^z.length) * fderiv ℝ (roc F z) p' (r • a)=_; rw [map_smul]; simp only [pow_succ,smul_eq_mul]; ring; exact (Lis.smooth k 1 z hk (by omega)).differentiableAt (by simp)
         exact hV p z k _ h
    rw [he' z hm, abs_mul,abs_pow]; exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) he)
end YM.MSbar.RawP
