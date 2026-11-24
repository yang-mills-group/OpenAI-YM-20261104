import YM.MS.Image.Seal
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
/-!
# Param charts arbitrary normed E, cost. Scope polynomial in all log scales.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Outlook
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock Emit
open Signal Book Convolve Garment.Wave Garment.Wick High Detect Domain Tone.Frame
open scoped Topology ContDiff Interval
variable {I E:Type} {G:Gauge}{X Y F:T ( Flats G)}{J N:Flats G}{f g p q:T (Coat G)}{b c:Bool}{t r:ℤ}{a h n m k ℓ:ℕ}{i:ℂ}{s y:ℝ} {U:Rip G} {K:Mob G}[NormedAddCommGroup E][NormedSpace ℝ E]
open ContinuousLinearMap
-- every tested chart real finite artefact; costs on all.
lemma BigG (hp:kPrice K)(n:ℕ)(v:Touch G n E): veg 0 (fun _:Unit=> fieldVal ( K n) v) 1:= by
    suffices he:∃ (F:Type) (_i:NormedAddCommGroup F) (_e:NormedSpace ℝ F) (_a:FiniteDimensional ℝ F) (w:Touch G n F) (L:E→L[ℝ] F),∀ x, sail v x=sail w (L x) by
       obtain ⟨F,u,U,hF,w,L,h⟩:= he; rw [show fieldVal (K n) v=(fun p=>fieldVal (K n) w (L p)) from funext fun p=> congr_arg _ (h p)]; exact Bound.linear L ( hp n F w)
    induction v with
    | nil=> exact ⟨ ℝ,inferInstance,inferInstance,inferInstance,[],0,fun _=>rfl⟩
    | cons i w ih=>
        obtain ⟨F,u,H,hF,w',L,h⟩:=ih; refine ⟨ SectorP n× F,inferInstance,inferInstance,inferInstance, (i.1, ContinuousLinearMap.fst ℝ _ F)::Wire.lift w' (snd ℝ _ F), i.2.prod L,?_ ⟩; intro p; simp only [sail_cons, lift_sail,h]; rfl -- fix snd_prod names
lemma mix_slide {V:ℝ→Mob G}{R:ℕ} (hp:V∈ Logarithm.interest R (Mob G))(_hP:∀ i, kPrice (V i))(w:Touch G n E)(x:ℂ)(s y:ℝ)(p:E): fieldVal (plow x s ( V (y+s)) n) w p =∑ i∈ Finset.range R, ( Logarithm.plate R i ).eval (y+s) • Alps.Bench.Forest.patch (fieldVal ( V i n) w) (x+mass w) s p:= by
   rw [interpret hp (y+s), Logarithm.evaluate, ← cert,map_sum]; simp_rw [fieldVal,Finset.sum_apply, show ∀ i, plower x s (( plate R i).eval (y+s) • V (i:ℝ)) =(plate R i).eval (y+s) • plow x s (V (i:ℝ)) from fun i=> map_smul ( (plower (G:=G) x s).restrictScalars ℝ) _ _]; apply Finset.sum_congr rfl; intro i _; simp only [Pi.smul_apply]; exact congr_arg (( (plate R i).eval (y+s) ) • · ) (s_p_vector (V (i:ℝ)) w p s x) -- type judgement
lemma full_sm (hp:Host J h)(y:ℝ)(w:Touch G n E) : ContDiff ℝ ∞ (fun z:ℝ × E=> fieldVal (hereZ h J z.1 y n) w z.2):= by
   obtain ⟨u,H⟩:= tallP ( Moony.toast hp.bill); let q(s:ℝ):= Press J u u s; obtain ⟨N,hN⟩:= (show Ready q from press_ready u); change _root_.ContDiff ℝ ∞ _; simp_rw [ vertical H hp.tall ]; change ContDiff ℝ ∞ (fun z:ℝ× E=> fieldVal (plow _ z.1 (q (y+z.1)) n) w z.2); simp_rw [mix_slide (V:=q) hN (pressB H u) w]; apply ContDiff.sum; intro i hi; have hu(i:ℝ): ContDiff ℝ ∞ ( fieldVal (q i n) w):= ( BigG ( pressB H u i) n w).smooth (); refine ( ( show ContDiff ℝ ∞ (fun t:ℝ=>(plate N i).eval t) from (by simpa using Polynomial.contDiff_aeval (𝕜:=ℝ) (plate N i) ∞)).comp (f:=fun z:ℝ×E=> (y+z.1)) (by fun_prop)|>.smul ( Bench.Forest.patch_w (hu _) ..) ) -- parse fun_prod composition
lemma hair (hp:Host J h)(w:Touch G n E): ContDiff ℝ ∞ (fieldVal (hereZ h J s y n) w):= ( BigG (blade0 hp).price n w).smooth ()
lemma trek (he:Host J h)(ht:Host N h)(hp: Vibe h J N)(v: Wire (Branch G Axis) E Detect.FourP): Domain.Track b (four h J) (four h N) v:= by
   have hx (i:ℝ): Alps.BothZ (fun s=>fieldVal (hereZ h J s i 0) v) (fun s=>fieldVal ( hereZ h N s i 0) v):=
       ⟨fun _=> hair he (n:=0) v,full_sm ht i (n:=0) v, fun x s=> rise he.tall ht.tall ( Moony.toast he.bill) hp s i 0 (sail v x) ⟩
   intro H; exact ⟨fun ⟨y,t⟩=> hair he (n:=0) v, fun ⟨y,t⟩=> hair ht (n:=0) v,fun i t x k=> (hx i).axes t k x⟩ -- fix name
lemma roadB (hx:leader G F f p): Domain.Flow ( spaceD G) true 1 ((2:ℂ)⁻¹) (Archive 4 F) (Archive 4 F):= by
   intro E _ _ w n hn hw; rw [← Bday hx hn]; exact trek (Host.host ( gang (hx n))) ( grow_host hx n ) (RootF (hx n)).advance w
lemma roadM (hx:leader G F f p)(hp:comet h r F g Y q) : Domain.Flow ( spaceD G) false 0 1 (Archive 4 F) (Archive h Y):= by
    intro E _ _ w n hn hw; rw [← Mday hx hp]; exact trek (Host.host ( gang (hp n))) ( mark_h hx hp n ) ( RootF (hp n)).advance w
end YM.MS.Outlook
