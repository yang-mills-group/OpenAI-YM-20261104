import YM.MS.Vibe.Cut
/-!
# Power momentum-interpreted derivative of anomaly

Keeping $ℓ$-sector unresolved on RHS. used on same mesh of F-equations at all log units s. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Emit
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{X Y F: T (Flats G)}{J N L:Flats G}{f g p q:T (Coat G)}{b c:Bool}{t r:ℤ}{a h n m k ℓ:ℕ}{i:ℂ}{s y:ℝ}
local notation "V" t => Grid i y t G
lemma high_u (h:leader G X f g)(n:ℕ): ∀ᶠ i in dotty,∀ s y, File i s y 5 ( PB X) n= (Grid i y s G).matCont ( File i s y 4 X) n := masterRow (Host.host ( gang (h n))|>.bill) 4 _ -- arguments param λ Pose dot binder
lemma bq_l (hp:comet h r X p Y q)(n:ℕ): ∀ᶠ i in dotty,∀ s y,File i s y (h+1) ( PM X Y) n=(Grid i y s G).res (File i s y 4 X) ( File i s y h Y) n:= by filter_upwards [masterRow (X:=X) (Host.host (gang (hp n))|>.bill) h 1] with i hi s y; unfold PM GridR.res; simpa only [one_smul] using hi s y
lemma start (h:leader G X f g)(n:ℕ): ∀ᶠ i in dotty,∀ s y m,∀ w:Legs (Shore G m), net w=0→ HasDerivAt (fun t=> File i t y 5 (PB X) n m w) ((Grid i y s G).lives ( File i s y 4 X) ( File i s y 5 ( PB X)) n m w) s:= by
   filter_upwards [high0, (eventually_all_finset (Finset.Iic n)).mpr (fun i _=> leaf h i), (eventually_all_finset (Finset.Iic n)).mpr (fun i _=> high_u h i)] with i hi ht hW s y m w hw; let S(t):= Grid i y t G; let F(t):=File i t y 4 X; -- ht all ≤n packaged
   have hm (t): Agree n ( File i t y 5 (PB X)) ((S t).matCont (F t)):= fun j hj=> hW j (Finset.mem_Iic.mpr hj) t y; simp_rw [hm _ n le_rfl]; rw [Agree.lives (show Agree n (F s) (F s) from fun _ _=>rfl) (hm s) (S s) n le_rfl]; exact trunc_m y (script i 4 X) (fun j hj=> ht j (Finset.mem_Iic.mpr hj)) hi s w hw -- fix names
lemma pinion (hx:leader G X f g)(hp:comet h r X p Y q)(n:ℕ): ∀ᶠ i in dotty,∀ s y, speed (fun t=> File i t y (h+1) (PM X Y) n) ((((Grid i y s G).lives (File i s y 4 X) (File i s y (h+1) (PM X Y)))+pairW (Grid i y s G).X ( File i s y 5 ( PB X)) ( File i s y h Y)) n) s:= by
   filter_upwards [high0,( eventually_all_finset (Finset.Iic n)).mpr (fun i _=> leaf hx i), (eventually_all_finset (Finset.Iic n)).mpr (fun i _=> aerial hx hp i), (eventually_all_finset (Finset.Iic n)).mpr (fun i _=> high_u hx i), (eventually_all_finset (Finset.Iic n)).mpr (fun i _=> bq_l hp i)] with i hi hF hQ hu hv s y
   let S(t):=Grid i y t G; let A(t):= File i t y 4 X; let B(t):=File i t y h Y; have hu(t): Agree n ( File i t y 5 ( PB X)) ((S t).matCont (A t)):= fun j hj=> hu j ( Finset.mem_Iic.mpr hj) t y; have hh(t): Agree n (File i t y (h+1) (PM X Y)) ((S t).res (A t) (B t)):= fun j hj=>hv j ( Finset.mem_Iic.mpr hj) t y; simp_rw [hh _ n le_rfl]; rw [ Agree.add ( Agree.lives (show Agree n (A s) (A s) from fun _ _=>rfl) ( hh s) ( S s)) (Agree.pair ( hu s) (show Agree n (B s) ( B s) from fun _ _=> rfl) ( S s).X) n le_rfl]; exact trunc_q y (fun i hi=> hF i (Finset.mem_Iic.mpr hi)) (fun i hi=>hQ i (Finset.mem_Iic.mpr hi)) (F:=script i 4 X) (X:= script i h Y) hi s -- fix
end YM.MS.Emit
