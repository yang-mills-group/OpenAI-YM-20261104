import YM.WilsonCoeffUV.Kinetic.Rep
import YM.UVExt.DualTiles
/-!
# From same two real waves amplitude budgets to the anchored cost

Limited to this thermal lookup. No translation-invariance shortcuts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Near Stationary PowerSeries Roam Asymptotics
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge}{s A B:ℝ}{R: PathData G}{p:Clip}{e:ℕ}

-- periodization in anchored basis
lemma act_bed (P:Row (Hooks G) (Hooks G))(n:Side): lagoon (orbQ (shuttleM P)) n= orbQ (P.acts n):=by
    funext x; apply Eq.trans ((tuck.tsum_eq (flair x (orbQ (shuttleM P)))).symm); unfold orbQ Row.acts; rw [Matrix.of_apply,← tsum_div_const]; apply tsum_congr
    intro j
    have ht: trope x (tuck j) ↔ (x 1).1=(x 0).1+wrap n j:=by
       unfold trope; constructor
       · intro h; rw [add_comm (x 0).1]; apply eq_add_of_sub_eq; exact (show _ from h 1)
       intro h i; fin_cases i; · simp [feetP]
       specialize h; change (x 1).1-(x 0).1=wrap n j; rw [h,add_sub_cancel_left]
    split <;>rename_i he; rw [flair_hit (ht.mpr he)]; unfold plantern shuttleM; simp [goose,feetP]; rfl
    rw [flair_miss (ht.not.mpr he),_root_.zero_div]
lemma plain_act (G:Gauge){H: FreeResolvent.FaceRow}(n:Side)(v:H.strip s A)(h:0≤s): lagoon (orbQ (plain G H)) n= orbQ (precisionC G n H):=by
    have he:(plaster G H).acts n=precisionC G n H:= by ext i j; rw [plaster,coloration_act,hBlock_periods h v]; rfl
    rw [← he]; exact act_bed _ _

-- waves bounded by one on reconstruction
abbrev monicℂ (n:Side):= ((n.val:ℂ)^4)⁻¹
def saxon (x:Woods G n)(p:Site n) (b : TypeFace 1)(i:G.ColorIndex):ℂ:= monicℂ n *∑ j:Site n,(cell p j)⁻¹ * ((arm G n 1 (Blue.pebble x) (j,b) i:ℝ):ℂ)
lemma sailorC (x: Woods G n)(p:Site n)(b:TypeFace 1)(i:G.ColorIndex) : ‖saxon x p b i‖ ≤ 1 :=by
    rw [saxon,norm_mul]; apply mul_le_one₀
    · unfold monicℂ; rw [norm_inv,norm_pow]; apply inv_le_one_of_one_le₀; apply one_le_pow₀; simp only [Complex.norm_natCast]; exact_mod_cast n.pos
    · positivity
    rw [Finset.sum_eq_single x.1]
    · rw [norm_mul,norm_inv]; have he : ‖cell p x.1‖=1:=by unfold cell; exact mode_real _ _ (real_frequency _)
      rw [he,inv_one,one_mul, Complex.norm_real,Real.norm_eq_abs];
      rw [arm_apply,Blue.pebble]; by_cases h:(x.1,b,i)=x <;> simp [h]
    · intro y _ h; have ht : (y,b,i)≠x:=fun hx=>h (congr_arg Prod.fst hx); rw [arm_apply,Blue.pebble]; simp [ht]
    simp
lemma flute (x:Woods G n) : ∑ p: Site n, wave p (saxon x p)=arm G n 1 (Blue.pebble x):=by
    let A:=saxon x; let v:=arm G n 1 (Blue.pebble x); let s:=monicℂ n
    funext p; ext l
    have hv : (fun t:G.Color=> t l) (∑ i: Site n, wave i (A i) p)= ∑ i: Site n,wave i (A i) p l := map_sum (PiLp.proj (𝕜:=ℝ) (2:ENNReal) (fun _=>ℝ) l) _ _
    rw [Finset.sum_apply]; change (fun t:G.Color=> t l) _= v p l; rw [hv]; change (∑ i:Site n,Complex.reCLM (cell i p.1*A i p.2 l))=v p l; rw [← map_sum]
    simp_rw [A,saxon,mul_left_comm _ (monicℂ n),←Finset.mul_sum]; let b (j:Site n):ℂ:=(v (j,p.2) l:ℝ)
    change (monicℂ n*(∑ i,cell i p.1 * ∑ j,(cell i j)⁻¹*b j)).re= v p l
    rw [UVExt.Paths.Covering.wave_rows, inv_mul_cancel_left₀ (pow_ne_zero 4 (by exact_mod_cast n.property.ne'))]; rfl

lemma timbre {x y: fieldDir G n 1→ℝ}( _p: Green (x ∘ arm G n 1))(_q:Green (y ∘ arm G n 1))(g:ContDiffAt ℝ ω x 0)(hh:ContDiffAt ℝ ω y 0)(w:∀ (i j: Site n) σ τ,(∀ k l,‖σ k l‖ ≤1) → (∀ k l,‖τ k l‖ ≤1) → ∀ v:Fin 2→fieldDir G n 1,v=![wave i σ,wave j τ]→ |iteratedFDeriv ℝ 2 x 0 v-iteratedFDeriv ℝ 2 y 0 v|≤A) (i:Fin 2→ Woods G n):
    ‖rye (x ∘ arm G n 1) 2 i-rye (y ∘ arm G n 1) 2 i‖≤ (1/2:ℝ)*(Fintype.card (Site n):ℝ)^2*A:=by
    let X:=iteratedFDeriv ℝ 2 x 0; let Y:=iteratedFDeriv ℝ 2 y 0; let L:= (arm G n 1).toContinuousLinearMap; let z: Fin 2 → _:= L ∘ Blue.pebble ∘ i
    have hs j := flute (i j)
    let f j (k:Site n):= wave k (saxon (i j) k); have hv:z=(fun j=> ∑ k,f j k):=funext fun j=> (hs j).symm
    have hz : |X z-Y z|≤ (Fintype.card (Site n):ℝ)^2*A:=by
       rw [hv,show X (fun j=>∑ k,f j k)=_ from X.toMultilinearMap.map_sum f,show Y (fun j=>∑ k,f j k)=_ from Y.toMultilinearMap.map_sum f, ← Finset.sum_sub_distrib]
       apply (Finset.abs_sum_le_sum_abs _ _).trans; refine (Finset.sum_le_sum (g:=fun _=>A) ?_).trans_eq (by simp); intro j _; exact w (j 0) (j 1) _ _ (sailorC (i 0) (j 0)) (sailorC (i 1) (j 1)) _ (funext fun s=>by fin_cases s<;>rfl)
    unfold rye; have he: iteratedFDeriv ℝ 2 (x ∘ arm G n 1) 0 (Blue.pebble ∘ i)= X z:= by
        change iteratedFDeriv ℝ 2 (x ∘ L) 0 _= _; rw [wired L ?_,map_zero]; rw [map_zero]; exact g.analyticAt
    have hw: iteratedFDeriv ℝ 2 (y ∘ arm G n 1) 0 (Blue.pebble ∘ i)= Y z:= by
        change iteratedFDeriv ℝ 2 (y ∘ L) 0 _= _; rw [wired L ?_,map_zero]; rw [map_zero]; exact hh.analyticAt
    rw [he,hw,← smul_sub,norm_smul]; refine (mul_le_mul_of_nonneg_left hz (norm_nonneg _)).trans_eq ?_; norm_num; ring
open Tree
variable {f c:Side} {S:StepData c f}{F:Forest S.ratio}{u:Clip}{Ñ:ChartRatio G}{ρ: fieldDir G c 1 →AxisChart G F}
variable {α Θ γ Λ:ℝ}{T: PathData G}
-- on two-point read
lemma thermal_coin (q:FiniteBound F R T u p α Ñ ρ Θ γ Λ)(i:Fin 2→ Woods G c):
    ‖rye (pointTherm S F R u ρ Ñ) 2 i-rye (draft (c:=c) α T p ∘ arm G c 1) 2 i‖ ≤ (1/2:ℝ)*(Fintype.card (Site c):ℝ)^2*((Fintype.card (Site c):ℝ)*Θ*Λ*Real.exp (-γ*c.val)) := by
    refine timbre (x:=thermal F (tac S) u R ρ Ñ) (thermC S F q) ?_ (q.born (tac S)) q.classicalResult ?_ i; swap
    · rintro i j a b ht hp _ rfl; exact q.wave_price _ _ _ _ _ ht hp
    all_goals first| exact q.born (tac S) | exact q.classicalResult | exact (show ContDiffAt ℝ ω _ (arm G c 1 0) from by rw [map_zero]; exact q.classicalResult).comp _ (arm G c 1).contDiff.contDiffAt

lemma draft_rate (h:T.Bounds p s A B)(n:Side)(u:ℝ):
    rye (draft (c:=n) u T p ∘ arm G n 1) 2=u • front T p n 0 2+front T p n 2 2:=by
    let H:=inputSeries (m:=n) p T; let X:=turnSeries T.loop (m:=n); let Y:=turnSeries T.cubic (m:=n); let V:=turnSeries T.quartic (m:=n);
    have hv: Green H:=(stain_knit T p h (m:=n)).analytic.contDiffAt
    have hX:Green X:= (turns_analytic _ h.width h.two).contDiffAt; have hY: Green Y:= (turns_analytic _ h.width h.three).contDiffAt; have hV: Green V := (turns_analytic _ h.width h.four).contDiffAt
    have he k (P: ℕ → Atom G k)(v:k>2) (hP:SumBudget (fun i=>(P i).budget s) A): rye (turnSeries P (m:=n)) 2=0:= by
       funext x; unfold rye; rw [(rays_jet (turns_analytic _ h.width hP) k).1 (turns_low _ h.width hP) 2 v]; simp
    have hr : front T p n 2 2=rye X 2:= (frontr h 2 1 n).trans (loop_axis h n).symm
    rw [show draft (c:=n) u T p ∘ arm G n 1 = u • H+X from rfl, rye_plus (u • H) X (show Green (u • H) from hv.const_smul u) hX,rye_mu _ _ hv, hr]
    unfold front; simp only [Pi.add_apply]; unfold sprig; rw [Nat.add_zero,shine_lit,shine_dark (by omega),add_zero,intent];
    change _=u • rye (H+Y+V) 2 + _; rw [rye_plus (H+Y) V (hv.add hY) hV,rye_plus H Y hv hY, he _ T.cubic (by omega) h.three,he _ T.quartic (by omega) h.four]; simp

-- enough tail with exactly side growth
lemma spectral_gain (Θ Λ γ:ℝ)(p:0<γ)(n:ℕ→Side)(he:Tendsto n atTop atTop):
    Tendsto (fun i:ℕ=> (1/2:ℝ)*(Fintype.card (Site (n i)):ℝ)^2*((Fintype.card (Site (n i)):ℝ)*Θ*Λ*Real.exp (-γ*(n i).val))) atTop (𝓝 0):=by
    let x i:= γ*((n i).val:ℝ)
    have h :Tendsto x atTop atTop:= Tendsto.const_mul_atTop p (tendsto_natCast_atTop_atTop.comp (by exact (show Tendsto Subtype.val (atTop:Filter Side) (atTop:Filter ℕ) from tendsto_atTop.mpr (fun k=> (eventually_ge_atTop (⟨k+1,k.succ_pos⟩:Side)).mono fun n hn=> Nat.le_trans (by omega) (show k+1 ≤ n.val from hn))).comp he))
    have hz:=((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 12).comp h).const_mul ((1/2*Θ*Λ/γ^12):ℝ)
    simp only [mul_zero] at hz; apply hz.congr; intro i; unfold x; simp; field_simp
end YM.WilsonCoeffUV.Bank.Mosaic
