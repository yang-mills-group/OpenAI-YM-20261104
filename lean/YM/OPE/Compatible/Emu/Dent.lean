import YM.OPE.Compatible.Emu.World
import YM.OPE.Compatible.Anchor.Rune
import YM.UVNext.COUPLING_RESET.Regular
import YM.OPE.Compatible.Begun.Vigor
import YM.Work.F03.Calculus
import YM.Next.RANK.Haar
/-!
# Uniform quadratic interior costs, no license yet
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score Tree Woody Next.Free FreeResolvent
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance
variable {i j d k m r l:ℕ}{n:Side}{K:Sponsor G}{T:Seasons K}{v:ℝ}
local notation "L!"=>Body 1 n
local notation "P!"=>Chamber G r
variable (p:Clip)(Y:PathData G)
lemma nonQ (U:Config G n):0 ≤ quadratic p Y U:= sum_nonneg fun i _=> add_nonneg (mul_nonneg p.quadratic_pos.le (G.price_range _).1) (by positivity)
lemma frag₀ (U:Config G n):0 ≤ secondTerm p Y U:= mul_nonneg (by positivity) (sum_nonneg fun i _=> nonQ _ _ _)
noncomputable abbrev seat :ℝ:= Fintype.card Signed
lemma seatK : 0<seat:=by unfold seat; exact_mod_cast Fintype.card_pos
noncomputable abbrev plateC (p:Clip):ℝ:=p.direct/2/ seat
lemma plateH :0<plateC p:=div_pos (by have h:=p.quadratic_pos; linarith) seatK
lemma cubicS (U:Config G n)(x:Face (Per n)): plateC p* G.chord (faceValue U x)^2 ≤ secondTerm p Y U:=by
       let f:= fun b:Face (Per n)=> p.direct*G.price (faceValue U b)+ ‖Y.ell U b‖^2/2; have he(i:Face (Per n)) :0 ≤ f i:= add_nonneg (mul_nonneg p.quadratic_pos.le (G.price_range _).1) (by positivity)
       have hs: f x ≤ quadratic p Y U:=single_le_sum (fun i _=>he i) (mem_univ x); let g(t:Signed):= quadratic p Y (pull t 0 U); have hv: quadratic p Y U=g 1:=by unfold g; rw [pull_id]
       rw [hv] at hs; have hp: g 1 ≤ ∑ i,g i:= single_le_sum (f:=g) (fun i _=>nonQ p Y (pull i 0 U)) (mem_univ _); calc
            _ = seat⁻¹ * (p.direct*G.price (faceValue U x)):=by rw [G.chord_price]; unfold plateC; ring
            _ ≤ seat⁻¹ * ∑ i,g i:=mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right (show 0 ≤ ‖Y.ell U x‖^2/2 by positivity)).trans (hs.trans hp)) (by have h:=seatK; positivity)
            _ = _:=rfl
lemma second_zero (R:PathData G)(P:Clip) : Flume.Script.swornX R P (0:Bid.Dir G n)=0:=by unfold Flume.Script.swornX; rw[Function.comp_apply,Precision.link_one,UVNext.CouplingReset.second_one]
variable (G)
variable (hp:Board n (r+2))
noncomputable abbrev sift :=sailT G (tip hp (show r+1 ≤ r+2 from Nat.le_succ _))
structure BayH (C:ℝ) (f:Bid.Dir G n→ℝ):Prop where
      grant : ∀ x:P!, C*‖x‖^2 ≤ iteratedFDeriv ℝ 2 f 0 ![sift G hp x,sift G hp x] -- weights supply
variable {G}
noncomputable abbrev damp (r:ℕ)(p:Clip):ℝ:= plateC p/(2*CloudH.taxC r)^2
lemma dampK (r:ℕ):0 < damp r p:=by have hv:=plateH p; have hp:=CloudH.taxNL r; have hs:=zero_lt_one.trans_le hp; unfold damp; positivity
lemma CloudPort (U:Config G n)(R:ℕ)(h:∀ e,e∉fringe R n→ U e=1):CloudH R 0 (Real.sqrt (secondTerm p Y U/plateC p)) U :=by
        have he:=plateH p; refine ⟨le_rfl,Real.sqrt_nonneg _,fun e hv=>?_,fun i _=>?_⟩
        · rw [h e hv,G.chord_one]
        let t:=secondTerm p Y U/plateC p; have ht:0 ≤ t:=div_nonneg (frag₀ _ _ _) he.le
        apply (sq_le_sq₀ (G.chord_nonneg _) (Real.sqrt_nonneg t)).mp; rw [Real.sq_sqrt ht,le_div_iff₀ he,mul_comm]; exact cubicS ..
-- arbitrary readings, removes arity from kernel conversion.
include hp in
private lemma horizonZ {I:Type}[Fintype I](x:Libra.Keys G I) (b:I→Edge (Site n))(f:ℝ→ Config G n) (he:∀ t i,f t (b i)=G.lieExp ((t • x:Keys G I) i))(hx:∀ t e,e∉fringe r n→ f t e=1):∀ᶠ t:ℝ in 𝓝 0,damp r p*‖t • x‖^2 ≤ secondTerm p Y (f t):=by
      let q (t:ℝ):= t • x; let m:=plateC p; let D(t:ℝ):= secondTerm p Y (f t); let B(t:ℝ):=Real.sqrt (D t/m)
      have hm:0 < m:=plateH p; have hS(t:ℝ):0 ≤ D t:= frag₀ _ _ _ ; have hY(t:ℝ):B t ^2 = D t/m:=Real.sq_sqrt (div_nonneg (hS _) hm.le); have hh(t:ℝ):CloudH r 0 (B t) (f t):= CloudPort p Y _ _ (hx _)
      have hv(j:I):∀ᶠ t in 𝓝 0,‖q t j‖/2 ≤ G.chord (f t (b j)):=by
            let A(t:ℝ):=t • x j; have hx:Tendsto A (𝓝 0) (𝓝 0):=(show A 0=0 from zero_smul ..) ▸ (show Continuous A by unfold A; fun_prop).tendsto 0
            apply (hx.eventually (Next.Rank.metric_law G)).mono; intro i hi; rw [he]; exact hi.1
      filter_upwards [eventually_all.mpr hv] with t ht; let c:=CloudH.taxC r; have hk:0<c:=zero_lt_one.trans_le (CloudH.taxNL r); have hB:=Real.sqrt_nonneg (D t/m); have hx:‖q t‖ ≤ 2*c*B t:=by
            refine (pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) hB)).mpr fun i=>?_ ; have h:‖q t i‖/2 ≤ c*B t:= (ht i).trans ((hh t).cup hp _|>.trans_eq (by rw [zero_add])); linarith only[h]
      change m/(2*c)^2 * ‖q t‖^2 ≤ D t; calc
           _ ≤ m/(2*c)^2 * (2*c*B t)^2:=mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) hB)|>.mpr hx) (dampK p r|>.le)
           _ = D t:= by rw [mul_pow (2*c),hY]; field_simp
include hp in
-- Kernel checker Work.O. declare hp₁ as extra
lemma oven (x:P!)(h:Board n (r+1)):∀ᶠ t:ℝ in 𝓝 0,damp r p * ‖t • x‖^2 ≤ Flume.Script.swornX Y p (t • sailT G h x):=by
      let f(t:ℝ):=represent (t • sailT G h x); have he(t:ℝ):f t=represent (sailT G h (t • x)):=congr_arg represent (map_smul (sailT G h) t x).symm
      have hh(t i):f t (dig h i)= G.lieExp ((t • x:P!) i):=by rw [he,holeS]
      exact horizonZ p Y hp x (dig h) f hh (fun t e hv=> (congr_fun (he t) e).trans (zeroRing G h (t • x) e hv))
-- transfer denominator in any E.Stability annotations
private lemma DampL {X E:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup E][NormedSpace ℝ E] (w:X)(z:E)(c:ℝ)(f:X→ℝ)(hf:ContDiffAt ℝ 2 f 0)(hz:f 0=0)(hy:IsLocalMin f 0)(hM:∀ᶠ t:ℝ in 𝓝 0,c*‖t • z‖^2≤ f (t • w)): 2*c*‖z‖^2≤ iteratedFDeriv ℝ 2 f 0 ![w,w]:=by
       have hd:fderiv ℝ f 0=0:=hy.fderiv_eq_zero; let Z(t:ℝ):= f (t • w); have hs:ContDiffAt ℝ 2 Z 0:=by unfold Z; exact (show ContDiffAt ℝ 2 f ((0:ℝ) • w) from by rw[zero_smul]; exact hf).comp (f:=fun t:ℝ=>t • w) _ (by fun_prop)
       have he:=Work.F03.taylor_limit_two hs (show Z 0=0 from by unfold Z; rw[zero_smul,hz]) (show deriv Z 0=0 from by rw [(Push.side f (hf.differentiableAt (by simp)) w).deriv,hd];rfl)
       have h:c*‖z‖^2 ≤ iteratedDeriv 2 Z 0/2:=by
           refine ge_of_tendsto he ?_
           filter_upwards [hM.filter_mono nhdsWithin_le_nhds,show ∀ᶠ t in 𝓝[≠] (0:ℝ), t≠0 from self_mem_nhdsWithin] with t ht hy
           rw [le_div_iff₀ (sq_pos_of_ne_zero hy)]; rw [norm_smul,Real.norm_eq_abs, mul_pow,sq_abs] at ht; exact (show c*‖z‖^2*t^2=c*(t^2*‖z‖^2) from by ring).trans_le ht
       have ht: iteratedDeriv 2 Z 0= _:= Work.F03.line_second hf hd w; rw[ht] at h; change 2*c*‖z‖^2 ≤ _; linarith only[h]
include hp in
lemma diagonalQ {x y:ℝ}(U:Y.Bounds p y v x)(h:Board n (r+1))(z:P!): 2*damp r p*‖z‖^2 ≤ iteratedFDeriv ℝ 2 (swornX Y p) 0 ![sailT G h z,sailT G h z]:=by
       let c:=damp r p; let f:= Flume.Script.swornX Y p (n:=n); have hf:ContDiffAt ℝ 2 f 0:= ((tubesY _ _ _ U).2).of_le le_top; have hz:f 0=0:=second_zero ..; have hy:IsLocalMin f 0:=by filter_upwards with i; change f 0 ≤ f i; rw [hz];exact frag₀ p Y _
       exact DampL (sailT G h z) z c f hf hz hy (oven p Y hp z h)
end YM.OPE.Merchant
