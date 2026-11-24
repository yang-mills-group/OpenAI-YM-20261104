import YM.MS.Vista.Style
/-!
# Bulk comparison on finite Mid to length-n. Cost books.L.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Rake.Geo
open scoped Topology ContDiff Interval
variable {I W E:Type}{G:Gauge}{M: Visa I}{P:Belt I}{L:I→Side}{N:Lin I}{F H X Y:Glade G I}{V K: Planet G I}
 {c s b:Bool}{k r:ℕ}{ S X': Rake.Site G I }{U:P.time→ℝ}{ A:Faces I}
abbrev Mid (M:Visa I)(L:I→Side):= midpoint M L
abbrev Miles (P:Belt I)(L:I→Side) (p: P.time):= dimT L p.1
local notation "Μ"=>Mid M L
local notation "Ω"=>enterV L b
variable {Q:ℕ→ I→Law G}
abbrev stepOne (M:Visa I)(L:I→Side)(K V:Planet G I): Prop:= Job.plug (J:= ( Mid M L ).slot ) (zoom K)=Job.plug (zoom V) -- for Mid μ compare Finite/cover
abbrev χr (P:Belt I)(i:ℕ)(F:Rake.Site G I):= WarpHere true true P ( F i ) ( rateS P 4 )
abbrev μF (P:Belt I)(L:I→Side)(p:P.time):= totalS ( Miles P L p )
abbrev μ0 (P:Belt I)(_:P.time):=planeF
lemma astral (x:(Mid M L).time) : ( Mid M L ).price.length x ≤ ( Miles (Mid M L) L x ).val:= le_trans ( AmountMX x |>.le ) ( lamp_m ( midT x|>.2 ) |>.trans_eq ( glowH L _ ) ) -- Tick L def.
lemma M_vel (h: Piece Μ K 1): Vel Μ (enterV L b) K (μF Μ L) 1:= ⟨ f_cap (fun i=> astral i), h,fun _=> zero_le_one ⟩
lemma χ_same (H:stepOne M L K V)(b:Bool): Prune Μ b K=Prune Μ b V:= funext fun i=> congr_arg (ηbone b) (congr_fun H i)
abbrev Billδ (ζ:Belt I)(L:I→Side)(d:ℝ)(k:ℕ):= goodM ζ d * gainQ ζ L k
lemma Bδ_η (P:Belt I)(L:I→Side)(x:ℝ)(k:ℕ): nn ( Billδ P L x k ):= joy ( pay_m _ _ ) (gain_pos _ _ _) -- remove ..
lemma gain_glue (h:r≤ k)(d:ℝ): Billδ Μ L d k ≤ Billδ Μ L d r:= fun _=> mul_le_mul_of_nonneg_left (gain_le h _) ( pay_m .. )
lemma m_lower (d:ℕ)(i:(Μ).time): gainQ Μ L d i=( ( Mid M L ).price.length i/( Miles Μ L i |>.val ) )^ d := rfl
lemma plateau {u:(Μ).time→ℝ}(hp:nn u)(he:Piece Μ K 1)(hv: stepOne M L K V)(hf:Toned F)(hh:Toned H)(hZ:SpanW c Μ ( F-H ) ( u* gainQ Μ L k ) (r+2))(hX: SpanW c Μ H u (r+2)): Spd c Μ ( CPlan Ω K F-CPlan ( outside L ) V H ) (u*gainQ Μ L k) r:= by
   let g:= ( gainQ Μ L k); let P:= Mid M L; let v (i:P.time):= σcap ( Miles Μ L i ); haveI (i:P.time):IsFiniteMeasure (v i):= finite_s ..; have hx :∀ x:P.time, Cour ( v x ):= fun _=> cour_s _; let A:=actorP P F; let B:= actorP P H; let T:= Prune P false K; let DU:= pClock v false 0 T; let DG:= pClock (fun (_:P.time)=> μzone) false 0 T; have h1:Visible A:= footage F hf; have h2:Visible B:= footage H hh; unfold Spd coinF; rw [map_sub];
   have hT: plug (bend G I ( CPlan Ω K F )-bend G I (CPlan (outside L) V H) ) = DU A-DG B:= by
      rw [show plug (J:=P.slot) (_-_) = plug (bend G I (CPlan Ω K F))-plug (bend G I (CPlan (outside L) V H)) from rfl, wc_click, wc_click ]; rw [ ← χ_same hv ]; rfl
   rw [ hT, show DU A-DG B= DU ( A-B )+( DU B-DG B) from (by rw [ show DU (A-B)=DU A - DU B from part_cut (K:=T) (b:=fun _=>0) hx (he false) h1 h2 (p:=false) ]; abel) ]; apply Lens.plus
   · have hζ : Lens c P.price (A-B) (u*g) (r+2):= by unfold SpanW at hZ; rw [map_sub] at hZ; exact hZ
     obtain hp':= p_pay (A:=fun _=>0) (μ:=v) (f_cap (Γ:=Miles Μ L) (fun i=> astral i)) ( he false ) ( visible_sub h1 h2 ) (p:=false) (fun x=>Bool.noConfusion x) hζ ( hh:=fun _=>zero_le_one) ( joy hp ( gain_pos P L k )); rw [one_mul] at hp'; exact hp'
   obtain hH:= p_diff (K:=T) ( N:= Miles P L )  (fun i=>astral i) ( he false ) h2 hX (hh:=fun _=>zero_le_one) hp k; apply Lens.up hH ; intro i; simp only [Pi.one_apply,Pi.mul_apply,m_lower ( M:=M ),one_mul]; rfl -- potential epsilon

end YM.MS.Vista
