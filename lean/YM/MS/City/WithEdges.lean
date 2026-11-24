import YM.MS.City.Classic
/-!
# Admissible integral operations for Points solution

Certificate all period cost-one operations. No total support required. Push through
 T products. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.City
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Landau Native Lattice Tone Momentum Heat Real Frame Wire
open Book Convolve
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{F H:BF (BH G) QP}{K L:ℝ→ Flux (BH G) QP ℂ}{t:ℝ}{A:Type}
-- fix absolute t lengths

lemma prodCour : Cour (μzone.prod μzone):= by
    let s:= firstZone Axis; letI : ProperSpace QP:= FiniteDimensional.proper ℝ QP;
    refine ⟨s×ˢ s,(isCompact_closedBall (0:QP) π).prod (isCompact_closedBall (0:QP) π),?_⟩; unfold μzone; rw [Measure.prod_restrict]; exact ae_restrict_mem (measurableSet_closedBall.prod measurableSet_closedBall)
-- Const word views.
variable [NormedAddCommGroup A][NormedSpace ℝ A]
def station (l: List (Lane4 G)): tagSmooth A (BH G) QP:= l.map fun i=> (i.1,fun _=>i.2)
lemma station_t (l:List (Lane4 G)): Trail (A:=BH G) (E:=A) (station l):= fun i hi=> by obtain ⟨a,ha,rfl⟩:= List.mem_map.mp hi; exact contDiff_const
omit [NormedAddCommGroup A][NormedSpace ℝ A] in
lemma station_w (l:List (Lane4 G))(x:A): walk0 (station l) x=l:= by simp [walk0,station,Function.comp_def]
lemma unload (h: TouchF F) (hx:flex K) (hk:flex L)(l:List (Lane4 G)) (t:ℝ): Integrable (fun u:QP×QP=>trc (L t) u.1 (trc (K t) u.2 (F t)) l) (μzone.prod μzone) := by
    apply cafe _ prodCour (f:=fun u:QP×QP=> _); apply ContDiff.continuous (n:=∞) (𝕜:=ℝ)
    let w:tagSmooth (QP×QP) (BH G) QP:= station l
    simp only [at_trc]; refine ContDiff.sum fun a _=> ContDiff.sum (fun b _=>?_)
    refine ((hk a b).comp (contDiff_const.prodMk contDiff_fst)).mul (ContDiff.sum (fun i _=> ContDiff.sum fun j _=> ((hx i j).comp (contDiff_const.prodMk contDiff_snd)).mul ?_));
    let S: tagSmooth (QP×QP) (BH G) QP:= [(i,Prod.snd),(j,-Prod.snd), (a,Prod.fst),(b,-Prod.fst)] ++ w; have hw : Trail S:= ((((Trail.cons (station_t l) b _ contDiff_fst.neg).cons _ _ contDiff_fst).cons _ _ contDiff_snd.neg).cons _ _ contDiff_snd) -- edit
    convert! h (QP×QP) (fun _=>t) S hw contDiff_const using 1; ext; simp [S,w,walk0,station,Function.comp_def]
lemma turns (h:TouchF F)(hr:flex K)(ht:flex L)(h':TouchF H)(l r:List (Lane4 G))(a e i j:BH G)(t:ℝ): ContDiff ℝ ∞ (hits parity (K t) (L t) (F t) (H t) l r a e i j) := by
    let V: tagSmooth QP (BH G) QP:= (a,id)::station l; let U:tagSmooth QP (BH G) QP:= (e,Neg.neg)::station r; have hV q:walk0 V q=(a,q)::l:= by change _::walk0 (station l) q=_; rw [station_w]; rfl
    have hU q:walk0 U q=(e,-q)::r:=by change _::walk0 (station r) q=_; rw [station_w]
    unfold hits; apply ((ht a e).comp (contDiff_const.prodMk contDiff_id)).mul; apply ContDiff.mul (by exact contDiff_const) ?_ -- metavars
    simp_rw [←hV,←hU]; exact radius1 (fun _=>t) contDiff_const hr i j h h' ((station_t l).cons _ _ contDiff_id) ((station_t r).cons _ _ contDiff_neg)
local instance : Measure.IsNegInvariant μzone:= capN
lemma cockpit (hf:TouchF F)(hg:TouchF H)(hP:Perk (F t))(hH:Perk (H t))(hx:flex K)(hk:flex L)(hV:Reverse (L t) parity)(hp:Near (K t))(ht:Near (L t)): Route (K t) (L t) parity (F t) (H t) μzone where
    lf l r a b i j:= Tone.integr _ ((turns hf hx hk hg l r a b i j t).continuous)
    rf l r a b i j:= by
        rw [show restL parity (K t) (L t) (F t) (H t) l r a b i j= (hits parity (K t) (L t) (F t) (H t) l r b a i j ∘ Neg.neg) from funext fun p:QP=> by simpa using RL (F:= F t) (H:= H t) (K:=K t) hV a b i j (l:=l) (r:=r) (-p)]
        exact Tone.integr _ ((turns hf hx hk hg l r b a i j t).continuous.comp continuous_neg)
    flip l r a b i j:= by rw [integral_neg_eq_self]
    shift l r a b i j:= by
        let W:= hits parity (K t) (L t) (F t) (H t) l r a b i j; change (∫ u,W (-(net l)-u) ∂μzone) = _; rw [show (∫ u,W (-(net l)-u) ∂μzone) = ∫ u,W (-net l+u) ∂μzone from (by simpa only [sub_eq_add_neg] using integral_neg_eq_self (f:= fun u:QP=> W (-(net l)+u)) (μ:=μzone))]; exact moves (-net l) (turns hf hx hk hg l r a b i j t).continuous (fun x q=> Perk.hit_steps x q a b i j l r hP hH hp ht)
lemma data0 (h:TouchF F)(hs:Symm (field parity) (F t)): Pieces0 (Cpu G t) (Mood G t) (Z G) μzone (F t) := by
   refine ⟨period0 μzone cour0 (main_f _) h, period0 μzone cour0 (mood_f _) h, ?_, ?_, ?_, period0 μzone cour0 (then_f _) h, (fun l=> unload h (main_f _) (mood_f _) l t), hs⟩
   · exact period0 μzone cour0 (main_f _) (loop_on μzone cour0 (mood_f _) h)
   · exact period0 μzone cour0 (mood_f _) (loop_on μzone cour0 (main_f _) h)
   exact period0 μzone cour0 (main_f _) (charge_touch (Z G) (flowSmooth G) h)
-- pre-built
lemma cert (t:ℝ) (F H:T (BF (BH G) QP))(hT:∀ i,TouchF (F i))(hK:∀ i,TouchF (H i))(hx:∀ i,Perk (F i t))(hq:∀ i,Perk (H i t))(hs:∀ i,Symm (field parity) (F i t))(hv:∀ i,Symm (field parity) (H i t))(hm:∀ i,Pure (field parity) false (F i t)): Pieces (Cpu G t) (Mood G t) (Z G) μzone (fun i=>F i t) (fun i=> H i t):=
    ⟨fun i=> data0 (hT i) (hs i), fun i=> data0 (hK i) (hv i), hm, fun i j=> period0 μzone cour0 (mood_f _) (tree_touch (Vrev G) (main_f _) (hT i) (hK j)), fun i j=> period0 μzone cour0 (main_f _) (tree_touch (Xrev G) (mood_f _) (hT i) (hK j)), fun i j=> cockpit (hT i) (hK j) (hx i) (hq j) (main_f _) (mood_f _) (Xrev G t) (L_stamp _) (X_stamp _), fun i j=>cockpit (hT i) (hK j) (hx i) (hq j) (mood_f _) (main_f _) (Vrev G t) (X_stamp _) (L_stamp _),X_even _ _,X_odd _ _,Y_odd _ _,Vrev _ _,Xrev _ _⟩
end YM.MS.City
