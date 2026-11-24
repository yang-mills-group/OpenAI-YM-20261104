import YM.RegulatorIR.Pupil.Dark

/-!
# Kernel moment debit at all vacuum ranks needing it.

Based on charge at held slots, bounds compatible with lower-outer recursive
differences. Trajectory input needs separate statement giving such charges.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Pupil
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Momentum Laurent WOne
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {G:Gauge}{I:Type}{p k u m e n r:ℕ}
variable {H C d b:ℝ≥0∞}
section Semi
variable (x:Foot G) (A:Fin r → CapG G) (t:Fin r→ Cover→ℝ)
def flume : Fin r→ BEdge G:=fun i=> scarf (area x) (A i) (t i)
def flame (i:Fin r)(v:Side)(j:Fin r):BEdge G:= if j=i then regalia (bonnet (lamps (A i) (area x)) v) else sachet (flume x A t j) v
lemma flameup (i:Fin r)(h:t i=1)(j:Fin r)(y:Foot G) : Tendsto (fun z=>hue (flame x A t i z j) y) atTop (𝓝 (hue (flume x A t j) y)):=by
 apply tendsto_const_nhds.congr'; by_cases he:j=i
 · subst i; unfold flame; simp_rw [if_true]; filter_upwards [rises_h (lamps (A j) (area x)) y.1] with z hz; unfold flume hue; rw [hz,lighting,h]
 unfold flame; simp_rw [if_neg he]; filter_upwards [rises_v (flume x A t j) y.1] with z hz; simp_rw [hue,hz]
lemma flame_g (i:Fin r)(v:Side)(j:Fin r): GivesT (flame x A t i v j):=by unfold flame; split; exact gives_reg (bonnet_v ..);exact sachet_s ..
lemma flame_t (i:Fin r) (z : Side) (P:∀ u:Fin r,∀ q,‖t u q‖ₑ≤1+Momentum.extent q) (j: Fin r) : TightF (area x) 3 (flame x A t i z j):=by
 unfold flame; split
 · exact (by simpa only [one_mul,show (1:ℝ≥0∞)+2=3 by norm_num] using tall_m (area x) (bonnet_h (area x) (cost_l (A i) (area x)) z))
 intro y; exact (sachet_h _ (shine_s (A j) _ _ (P j)) z y).trans (mul_le_mul_left (show (1:ℝ≥0∞)≤3 by norm_num) _)
variable {U:Orders (Foot G)} (h:W1 U p)(L:LowerQ U e u C)
variable (ht:Held (U e (r+1)) u b)(hp: r+1≤u)(hv:IsSym (U e (r+1)))(he:e≤p)(hJ:r+1≤e+2)
include ht h hJ L hp hv he
lemma torch (hb:b≠⊤) (i:Fin r) (hq: t i=1)(P:∀ j y, ‖t j y‖ₑ≤1+Momentum.extent y) : ‖matchT (U e (r+1)) (Fin.cons (pointA x) (flume x A t))‖ₑ ≤ cork G 3 1 e (r+1)*C:=by
 let T(z:Side): Fin (r+1)→ BEdge G:= Fin.cons (pointA x) (flame x A t i z)
 let c:ℝ≥0∞:= cork G 3 1 e (r+1)*C
 have hh(z): ‖matchT (U e (r+1)) (T z)‖ₑ≤ c:=by
    let F:=lamps (A i) (area x);let a:= bonnet F z
    apply oracle h L he hp hJ hv (T z) (bonnet_h (area x) (cost_l (A i) _) z) (fun k=>Fin.cases ?_ ?_ k) (bonnet_v _ z) (fun k=>Fin.cases ?_ ?_ k) 0 i.succ rfl i.succ_ne_zero
    · change flame _ _ _ _ _ _=_; rw [flame,if_pos rfl]
    · intro y; exact (peak_f (x:=x) (area x) y).trans (mul_le_mul_left (show (1:ℝ≥0∞)≤3 by norm_num) _)
    · intro k; exact flame_t x A t i z P k
    · exact gives_lone
    intro k; exact flame_g x A t i z k
 have hl:= glide_m hb (show (3:ℝ≥0∞)≠ ⊤ by finiteness) (le_trans (Nat.le_succ r) hp) ht (fun z j=>flame_t x A t i z P j) (flameup x A t i hq)
 apply le_of_tendsto' (x:=atTop) (f:=fun z=> ‖matchT (U _ _) (T z)‖ₑ) (b:=c) ?_ hh
 exact Filter.Tendsto.enorm hl -- name
omit h hJ L hp ht hv he
lemma partial_v (K:Packet (Foot G) (r+1)): matchT K (Fin.cons (pointA x) (flume x A t))= ∑' q:MovesR r, Momentum.anchored x K (charges (area x) A q)* ∏ i:Fin r,t i (confers q i):=by
 rw [match_h]; let F:= charges (area x) A
 let v(w:Tuple (Foot G) r):= Momentum.anchored x K w * ∏ i,hue (flume x A t i) (w i)
 let a:Foot G→CapG G:=tariff
 have hb(w:Foot G)(i:Fin r)(h:hue (flume x A t i) w ≠0): a w=A i:=by
    unfold hue flume scarf at h;split at h
    next hi => refine Prod.ext hi ?_; change w.2=_; by_contra ht; simp [singleR,ht] at h
    next hi=> simp at h
 have hh:Function.support v⊆Set.range F:=by
    intro i hi
    have h:a∘i=A:=funext fun j=> hb (i j) j fun hv=> hi (mul_eq_zero_of_right _ (prod_eq_zero (mem_univ _) hv))
    refine ⟨porter (area x) i,?_⟩
    have he:= (transport (area x) G.ColorIndex r).apply_symm_apply i
    change charges _ (fun j=>a (i j)) (porter (area x) i)= _ at he; rw [show (fun j=>a (i j))=A from h] at he; exact he
 unfold chargeT;rw [← (show Injective F from fun j k h=> Prod.mk.inj ((transport (area x) _ _).injective h) |>.2).tsum_eq hh];apply tsum_congr;intro v'
 unfold v; apply congr_arg (Momentum.anchored x K (F v') * ·); apply Finset.prod_congr rfl;intro i _; unfold hue flume scarf F charges ask; simp [singleR]
local notation "coast"=> cork G 3 1 e (r+1)*C
include h hJ L hp ht hv he
lemma zero_tick (hb:b≠⊤) (i:Fin r) (z: Sequence (Fin r× Axis) 0): ‖readsP ((Momentum.anchored x (U e (r+1)))∘ charges (area x) A) 0 z‖ₑ≤ coast:=by
 have hh:= torch x A (fun _=>1) h L ht hp hv he hJ hb i rfl (by intros;simp)
 rw [partial_v] at hh; simp only [Pi.one_apply,Finset.prod_const_one,mul_one] at hh
 simpa only [readsP, rateP,mul_one,comp_apply] using hh
lemma one_tick (hb:b≠⊤) (z: Sequence (Fin r× Axis) 1)(i:Fin r)(hi:i ≠(z 0).1) : ‖readsP (Momentum.anchored x (U e (r+1))∘ charges (area x) A) 1 z‖ₑ≤ coast:=by
 let y:=z 0; let t(j:Fin r)(v:Cover):ℝ:= if j=y.1 then v y.2 else 1
 have H:t i=1:=by ext v;exact if_neg hi
 have hh(j v): ‖t j v‖ₑ≤1+Momentum.extent v:=by unfold t;split; exact sky_pay ..; simp
 apply le_trans _ (torch x A t h L ht hp hv he hJ hb i H hh); rw [partial_v]; apply le_of_eq; apply congr_arg; apply tsum_congr; intro c; apply congr_arg
 unfold rateP; rw [prod_eq_single_of_mem y.1 (mem_univ _)]; swap; intro j _ he; exact if_neg he
 unfold t; rw [if_pos rfl];simp only [rateP,mul_one]; rfl

lemma prism_h (hb:b≠⊤)(hh:2≤r): MomentsP (U e (r+1)) (5-(r+1)) coast:=by
 intro x A i hi y; have hx:i ≤1:=by omega
 interval_cases i
 · let p:Fin r:= ⟨0,by omega⟩;exact zero_tick x A h L ht hp hv he hJ hb p _
 by_cases H:(y 0).1.val=0
 · exact one_tick x A h L ht hp hv he hJ hb y ⟨1,hh⟩ (Fin.ne_of_val_ne (by change 1≠_;omega))
 exact one_tick x A h L ht hp hv he hJ hb y ⟨0,by omega⟩ (Fin.ne_of_val_ne (by change 0≠_;omega))
end Semi
end YM.RegulatorIR.Pupil
