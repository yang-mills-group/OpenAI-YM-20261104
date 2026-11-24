import YM.MS.Wind.Closed
/-!
# Lattice chart flow to log-t family

Explicit flow derivative (all chart mixed derivatives) by log composition with
 integrated absolute-R station. Ready scaling bound from periodic after.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Wind
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Landau Native Lattice Tone Momentum Heat Real Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal High
open Complex (I)
open scoped Topology ContDiff
variable {G: Gauge}{p:Team}{φ: Actor G}{F H: Dec G}{u:ℤ} {k:ℕ}{l:List (Lane4 G)} {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
-- `coast`
lemma jointWay {F:Wind.Flow G}(h:TouchF F)(w:Wire (BH G) E QP): ContDiff ℝ ∞ (fun x:ℝ×E=> F x.1 (sail w x.2)):= by
   let v:tagSmooth (ℝ×E) (BH G) QP:= w.map fun i=>(i.1,fun x:ℝ×E=> i.2 x.2); have ht : ∀ x:ℝ×E,walk0 v x=sail w x.2:= by intro x; unfold v walk0 sail; simp only [List.map_map]; rfl
   simp_rw [←ht]; refine h (ℝ×E) _ v ?_ contDiff_fst; intro i hi; obtain ⟨a,ha,rfl⟩:= List.mem_map.mp hi; exact a.2.contDiff.comp contDiff_snd
lemma term_account {F H:Wind.Flow G}(_h:TouchF F) (hx:TouchF H)(hk:∀ t,Zip F (H t) t): F=(fun _=> F 0) + coast H:= by
   ext t l; let f (t:ℝ):=coast H t l; have he t : HasDerivAt f (H t l) t:=hfun ((hx.at_const id l contDiff_id).continuous) t; have hv t := (hk t l).sub (he t);
   let D t:= F t l-f t; have hR s: HasDerivAt D 0 s:= sub_self (H s l) ▸ hv s
   obtain ht:= constancy hR t; unfold D at ht; rw [show f 0=0 from (by simp [f,coast])] at ht -- D not unfolded
   exact sub_eq_iff_eq_add.mp (by simpa using ht) -- maybe order
lemma dual_log (F H:Wind.Flow G)(h:TouchF F)(hT: TouchF H)(hk:∀ t, Zip F (H t) t)(v: Wire (BH G) E QP)(t:ℝ)(i:ℕ) (x:E) : HasDerivAt (fun t=>iteratedFDeriv ℝ i (fieldVal (F (exp t)) v) x) (iteratedFDeriv ℝ i (fieldVal ((↑(exp t):ℂ) • H (exp t)) v) x) t:= by
    let Q : ℝ×E→ℂ := fun p=> H p.1 (sail v p.2); have hQ: ContDiff ℝ ∞ Q:= jointWay hT v
    have hv (t:ℝ): fieldVal (F (exp t)) v= fieldVal (F 0) v+ fun x=> desk Q (exp t,x):= by nth_rw 1 [term_account h hT hk]; rfl
    let V:= iteratedFDeriv ℝ i (fieldVal (F 0) v); have ht t : ContDiff ℝ ∞ (fun x:E=> desk Q (t,x)):= (park hQ).comp (show ContDiff ℝ ∞ (fun x:E=> (t,x)) by fun_prop);
    simp_rw [hv, iteratedFDeriv_add ((show ContDiff ℝ ∞ (fieldVal (F 0) v) from h.routine v 0).of_le (by exact_mod_cast le_top)) ((ht _).of_le (by exact_mod_cast le_top)),Pi.add_apply] -- fieldVal routine eta
    have he := ((deskD_iter hQ i (exp t) x).scomp t (Real.hasDerivAt_exp t)).const_add (V x);
    convert! he using 1
    rw [show fieldVal ((↑(exp t):ℂ) • H (exp t)) v=exp t • fieldVal (H (exp t)) v from rfl,iteratedFDeriv_const_smul_apply ((show ContDiff ℝ ∞ (fieldVal (H (exp t)) v) from hT.routine v (exp t)).contDiffAt.of_le (by exact_mod_cast le_top))]; rfl
-- log mapping

def col (F:Dec G): High.Recount G:= fun n s=> F n s.1 (exp s.2)
variable (x t:ℝ)
local notation "ξ" => Ω G
abbrev Svs (G:Gauge):= spaceL G
lemma weight_day : (spaceL G).meter t = (↑(exp t):ℂ) • Cpu G (exp t):= by
    funext i j q; simp only [spaceL,zL,Cpu,LegsK,Landau.choir,Pi.smul_apply,smul_eq_mul]; by_cases h:i.2=j.2 <;> simp only [h,↓reduceIte,mul_zero,brushed]
lemma lineC {F:Law G}{K:Flux (BH G) QP ℂ} (c:ℂ): cycle (c • K) μzone F=c • cycle K μzone F:= by
    funext w; unfold cycle; have he (q:QP): trc (c • K) q F w=c*trc K q F w:= by simp only [at_trc, Finset.mul_sum,Pi.smul_apply,smul_eq_mul,mul_assoc]
    simp_rw [he,integral_const_mul]; rfl
lemma lineT {F H:Law G}{K:Flux (BH G) QP ℂ} (c:ℂ): tree parity (c • K) F H=c • tree parity K F H:= by
    funext w; unfold tree; rw [show attaches parity (c • K) F H= c • attaches parity K F H from ?_]; exact map_smul (allocate (field parity) w) c _ -- fix
    funext l r; unfold attaches; simp only [Finset.mul_sum,Pi.smul_apply, smul_eq_mul, mul_assoc, mul_add]
lemma missionday (F H:Dec G)(c:ℝ)(n r:ℕ)(h:TouchF (H n x)) : (spaceL G).recu r (c:ℂ) (col F) (col H) n (x,t)=(↑(exp t):ℂ) • (Wiref G (H n x) (exp t)+ path c n r F H x (exp t)):= by
   unfold Domain.recu col Domain.using_tree; dsimp only; rw [weight_day];
   rw [show (spaceL G).measure=μzone from rfl,lineC,smul_add,show Wiref G (H n x) (exp t)= Ccy (Cpu G (exp t)) _ μzone from finite_cc μzone (period0 μzone cour0 (main_f _) h),quarterback];
   congr 1; simp_rw [lineT,← Finset.smul_sum,smul_comm (c:ℂ) (↑(exp t):ℂ)]; rfl
end YM.MS.Wind
