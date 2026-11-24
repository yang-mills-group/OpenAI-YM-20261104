import YM.MS.Image.Atlas
/-!
# High projected MS vertices satisfy 4D certificate
Spec projection includes Ward for seeded order series.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Outlook
open Set Filter Function Finset MeasureTheory Metric Arc Real Polynomial
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock Emit
open Signal Book Convolve Garment.Wave Garment.Wick High Detect Domain Tone.Frame Momentum
open scoped Topology ContDiff Interval
variable {I E:Type} {G:Gauge}{A B:T (Mob G)}{P Q:T (Coat G)}{X Y F:T (Flats G)}{J N:Flats G}{b:Bool}{t r:ℤ}{n m h:ℕ}{s y:ℝ} {K:Mob G}
-- polynomial in y uniform including t
private def slidePair(E:Type)[AddCommGroup E][Module ℝ E]: (ℝ→ℝ) →ₗ[ℝ] (ℝ→E) →ₗ[ℝ] (ℝ→E) where
    toFun x:={ toFun y:=fun s=>x s • y s,map_add':=fun f g=>funext fun i=>smul_add (x i) (f i) (g i),map_smul':= fun a y=> funext fun i=> smul_comm (x i) a (y i) }
    map_add' a b:= LinearMap.ext fun i=> funext fun z=> add_smul (a z) (b z) (i z)
    map_smul' k f:= LinearMap.ext fun i=> funext fun z=> mul_smul k (f z) (i z)
private lemma polyp (p:Poly): Ready (fun v t:ℝ=>p.eval (v+t)):= by
    induction p using Polynomial.induction_on' with
    | monomial n a=>
        have he: Ready (fun v t:ℝ=> v+t):= by have hp:= status Polynomial.X (fun _:ℝ=> (1:ℝ)); convert hp.add (Ready.const (id:ℝ→ℝ)) using 1; ext; simp
        have hx (n:ℕ) : Ready (fun v t:ℝ=> (v+t)^n):= by induction n with| zero=>simp; exact Ready.const _|succ n ih=>simp_rw [pow_succ]; exact ih.pair (slidePair ℝ) he
        simp_rw [Polynomial.eval_monomial]; exact Ready.scale (hx n) a
    | add p q hx hy=> simp_rw [Polynomial.eval_add]; exact Ready.add hx hy
private lemma jetLong {F:ℝ→Mob G}(h:Ready F)[AddCommGroup E] [Module ℝ E](L:ℝ→ (Mob G→ₗ[ℝ] E)): Ready (fun z:ℝ=> fun t:ℝ=> L t (F (z+t))) := by -- wrong binder typeclasses order
   refine h.Ind (p:=fun F=>Ready fun v:ℝ=>fun t:ℝ=> L t (F (v+t))) ?_ ?_ ?_ ?_
   · intro a x; simp_rw [map_smul]; exact Ready.pair (slidePair E) (polyp a) ( Ready.const _)
   · simp_rw [Pi.zero_apply,map_zero]; exact Ready.const _
   · intro x y hp hQ; simp_rw [Pi.add_apply,map_add]; exact hp.add hQ
   intro c x hx; simp_rw [Pi.smul_apply,map_smul]; exact hx.scale c
lemma plant (hp:Host J h) : High.stamp ( four h J ):= by
   obtain ⟨m,H⟩:= tallP (Moony.toast hp.bill); let L := (LinearMap.proj 0 : Mob G→ₗ[ℝ] Rack G 0); unfold High.stamp four; simp_rw [vertical H hp.tall]; exact jetLong ( press_ready m (n:=m) (F:=J)) (fun t=> L.comp ((plower (-(h:ℂ)) t).restrictScalars ℝ))
-- enum projection. Stamp cert conditional canonical physics
lemma dock (hx:leader G X (gloss A) P)(hv:Council A): Disc true 1 (Archive 4 X) (Archive 4 X) ((2:ℂ)⁻¹) 4:= by
   have ht n:= gang ( hx n ); refine ⟨{ road:= roadB hx,trueC:=fun i t=>antSolid (ht i) _,rank:=fun i=> bed ( ht i ),reflects:= fun i t _=> fleet ( ht i ) t,poly:= fun i=> plant ( Host.host (ht i)),qfm:= fun i ⟨y,t⟩ w h hw ht=> B_ward hx w ht ( wardLeader hx hv i|>.1 ) h },?_,?_⟩ -- align
   · intro E _ _ n w hw h; exact Billp w (Host.host (ht n))
   intro E _ _ n w hw h; exact Risep w ( Host.host ( ht n ))
lemma fieldD (hx:leader G X (gloss A) P)(hp: comet h 0 X (gloss B) Y Q)(hc: Council A)(he:Trill A B): Disc false 0 (Archive 4 X) ( Archive h Y ) 1 h:= by
    have ht k:=gang (hp k); refine ⟨{ road := roadM hx hp,trueC:=fun k t=> antSolid (ht k) t,rank:=fun k=> bed ( ht k ),reflects:= fun _ _ h=> Bool.noConfusion h,poly:= fun i=> plant (Host.host (ht i)),qfm:=fun i ⟨y,t⟩ w hw ht h=> M_ward hx hp ( wardMark hx hp hc he i|>.1) w },?_,?_⟩
    · intro E _ _ n w hw hv; exact Billp w ( Host.host ( ht n ) )
    intro E _ _ n w hw hv; exact Risep w ( Host.host ( ht n ) )
end YM.MS.Outlook
