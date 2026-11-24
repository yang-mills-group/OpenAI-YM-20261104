import YM.MS.Image.Front
/-!
# Sector projection at ζ=0 reinstates ordinary volume integration
 and momentum convolution with wavelength independent first-normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Outlook
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock Emit
open Signal Book Convolve Garment.Wave Garment.Wick High Detect Domain Tone.Frame
open scoped Topology ContDiff Interval
variable {I:Type} {G:Gauge}{X Y F:T ( Flats G)}{J N:Flats G}{f g p q:T (Coat G)}{b c:Bool}{t r:ℤ}{a h n m k ℓ:ℕ}{i:ℂ}{s y:ℝ} {U:Rip G}{T0':Mob G}
def four (s:ℕ)(F:Flats G) : Reading G:= fun (y,t)=> hereZ s F t y 0
def Archive (h:ℕ)(X:T (Flats G)): Recount G:= fun i=> four h (X i)
lemma no0 (h:ℕ)(t y:ℝ): hereZ (G:=G) h 0 t y=0:= by rw [hereZ,pageZ]; apply ruby0
lemma μcanon (y:ℝ)(h:Knot false U)(hp:Form0 false T0'): unitC 0 y U T0' 0= cycle (U 0) (covMeasure (Arts.L 0)) (T0' 0):= by
   ext w; simp only [unitC,LinearMap.smul_apply, port_spec (by simpa using Town_nat 0) _ h hp, fee_T0,Pi.smul_apply]; obtain ht:= lowN (m:=0) hp.price h.price hp.token h.token w; push_cast at ht; rw [ht,pitch]; simp only [Nat.factorial_zero, pow_zero,mul_one,Nat.cast_one,one_smul]; unfold cycle; rw [show covMeasure (Arts.L 0)=(ENNReal.ofReal room) • Px 0 from ?_,integral_smul_measure, ENNReal.toReal_ofReal room_pos.le]; rfl -- Pt maybe closes
   unfold room covMeasure Px; simp [Zed] -- might ENNReal parse from grep
-- Table at X.Sum. abstract Domain with DegreeMaster etc evaluation.
lemma card_Z (M:Needle G){F X : T (Mob G)} (hU: Knot false U) (hp:M.measure=covMeasure Axis)(hc:M.meter s=U 0)(n d:ℕ)(c:ℂ) (hf:Form0 false (X n))(B Y: Recount G)(hu:∀ i:ℕ,Y i (y,s)=X i 0)(hv:∀ i,B i (y,s)=F i 0)(he: pairW (squad U) F X n=∑ i∈ paths n d, squad U (F (n-i)) (X i)) : recu M d c B Y n (y,s)= (unitC 0 y U (X n)+c • pairW (squad U) F X n) 0:= by
   unfold recu using_tree; dsimp only; rw [hp,hc,he]; simp_rw [hu,hv, Pi.add_apply,Pi.smul_apply,μcanon _ hU hf, Finset.sum_apply]; rfl -- instances maybe proof arrays code
lemma corner_all (U: Oceans.Pair G) (F:T (Mob G))(n:ℕ)(hp:0<n)(hv:F 0=0): pairW U F F n=∑ i∈ paths n 1,U (F (n-i)) ( F i):= by rw [paired,Tone.Frame.canon_corner (fun i j=> U (F i) (F j)) n hp, hv,map_zero,map_zero,LinearMap.zero_apply,zero_add,zero_add]
lemma corner_mark (U: Oceans.Pair G) (F X: T (Mob G))(n:ℕ)(hv: F 0=0): pairW U F X n=∑ i∈ paths n 0,U (F (n-i)) (X i):= by rw [paired,Tone.Frame.canon_sub (fun i j=> U ( F i ) ( X j )) n, hv,map_zero,LinearMap.zero_apply,zero_add]
-- universal spin at outbox
lemma blade0 (hp:Host J h): Form0 false ( hereZ h J s y ):= just_bright hp.tall hp.bill
lemma archive0 (h:X 0=0)(ℓ:ℕ) : NumX s y ℓ X 0=0:= by unfold NumX; rw [h,no0]
lemma dayB (K:Needle G) (hp:Host (X n) 4)(he:X 0=0)(hM:K.measure= covMeasure Axis)(ht:K.meter s=U 0)(hU:Knot false U)(hx:0<n)(c:ℂ): recu K 1 c (Archive 4 X) (Archive 4 X) n (y,s)= (unitC 0 y U (NumX s y 4 X n)+c • pairW (squad U) ( NumX s y 4 X ) ( NumX s y 4 X ) n) 0:= card_Z K hU hM ht n 1 c (blade0 hp) _ _ (fun _=>rfl) (fun _=>rfl) ( corner_all _ _ n hx (archive0 he 4) )
lemma dayM (K:Needle G)(hp:Host (X n) h)(he:F 0=0)(hM:K.measure=covMeasure Axis)(ht:K.meter s=U 0)(hU:Knot false U) (c:ℂ): recu K 0 c (Archive 4 F) (Archive h X) n (y,s)=(unitC 0 y U (NumX s y h X n)+c • pairW (squad U) ( NumX s y 4 F) ( NumX s y h X) n) 0:= card_Z K hU hM ht n 0 c (blade0 hp) _ _ (fun _=>rfl) (fun _=>rfl) ( corner_mark _ _ _ _ (archive0 he 4) )
end YM.MS.Outlook
