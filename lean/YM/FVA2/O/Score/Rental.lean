import YM.FVA2.O.Score.Art
/-!
# Scaling algebra on the graded alphabet and Album

`squeeze` uses logarithmic parameter with shrinking sign; `CoinQ` inserts
engineering powers to go with it. This is scale-law bookkeeping used e.g. in
the FAR OPE.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Score
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open Dframe FVA2.Scale MS.Rake MS.Theater Level Facets Equator
variable {G:Gauge} { n m d k : ℕ }{x:Points n }{p:Scan G n}
variable {B:Cast G}{V F:Arenas G}{T:Frames G}
abbrev fee (t d:ℝ):ℂ:= (Real.exp (-t*d):ℝ)
abbrev squeeze (t:ℝ)(x:Points n): Points n:= ( Real.exp ( -t ) ) • x
abbrev Squeeze (t:ℝ)(A:Arenas G): Arenas G:= fun i=> scaling t (A i)
abbrev CoinQ (t:ℝ) (A:Album G): Album G:= fun n x v=> PowerSeries.C (fee t ( totalG v ))* A n ( squeeze t x ) v
lemma season (t:ℝ)(u:ℕ): Extent.token t u= fee t u:= by rw [ Extent.token,fee, Real.exp_mul, ← Complex.ofReal_pow, Real.rpow_natCast ]; -- ns?
lemma priced (t:ℝ)(p:Scan G n): ∏ i: Fin n, Extent.token t ( heft ( p i ) ) =fee t (totalG p):= by unfold Extent.token; rw [ Finset.prod_pow_eq_pow_sum ]; exact season t _
lemma squeeze_away (hc:x∈ conf n)(t:ℝ): squeeze t x∈conf n:= Extent.placed t x hc
lemma after (t:ℝ): squeeze (-t) ( squeeze t x )=x:= by unfold squeeze; rw [neg_neg,← mul_smul, ← Real.exp_add, add_neg_cancel,Real.exp_zero, one_smul ]
lemma squeeze_iff (t:ℝ)(x:Points n): squeeze t x∈conf n↔ x∈ conf n:= ⟨fun h=> ( after (x:=x) t ) ▸ squeeze_away h (-t), fun h=> squeeze_away h t ⟩
lemma squeeze_wall (h:Regular V)(t:ℝ): Regular ( Squeeze t V ):= fun _ _ he=> unfold_scale _ t he _ ( h _ _ he )
lemma scale_l (A:Arenas G)(t:ℝ): install ( Squeeze t A )= CoinQ t ( install A ) := by
    funext n x p; by_cases hp:x∈ conf n; swap; · simp [ CoinQ,install,hp,squeeze_iff ];
    rw [install,dif_pos hp,CoinQ,install,dif_pos ( squeeze_away hp t ) ]; refine PowerSeries.ext fun i=>?_ ; unfold Reg.Point.story Squeeze; rw [ coeff_mk, coeff_C_mul,coeff_mk, scale_at ];
    unfold tape cap Function.comp; simp_rw [ exact₀, low_size ]; rw [ MultilinearMap.map_smul_univ, priced ]; rfl
-- actual law.Superscript t. Notice inverse
variable {R:ℝ→Cn}{H:ℝ→Frames G}
lemma slot (h:Law V R H)(t:ℝ): Civil ( H t ) := ⟨ h.paid t,h.ready t,fun p=> h.continues t p ⟩
lemma rhythm_v (h:Law V R H): Town (fun t=> seats ( H t )):= scene_k h.proper
lemma rhythm_b (h:Law V R H): Town (fun t=> seats ( replay ( H t ))):= scene_k h.invert
lemma town (h:Law V R H)(hr:Regular V)(t:ℝ) : CoinQ t ( install V )= marking ( seats ( replay ( H t ) ) ) (tune ( R t ) ( install V )):= by
    let A:=Squeeze t V; have hp:= slot h t; let V:=V;
    rw [ ← scale_l,tune_live ( h.led t|>.start ) ]; rw [ unveil ( tune_reg hr ) hp.turn ]; refine congr_arg install (funext fun d=> ?_ ); unfold Mark TuneQ; rw [← h.reads, acts, ( hp.hue d ).turn', acts_h]; -- replay unfolding
lemma phase_l (h:Law V R H)(hr:Regular V)(t:ℝ) : marking ( seats ( H t )) ( CoinQ t ( install V ))= tune ( R t ) ( install V ):= by
    funext n x p; rw [ town h hr ]; unfold marking; rw [ ← concerto, spin_v ( slot h t ), soloist ] -- assoc
-- inverse fee
lemma fee_mul (t n:ℝ) : fee t n*fee (-t) n=1:= by unfold fee; rw [← Complex.ofReal_mul, ← Real.exp_add, neg_neg, neg_mul,neg_add_cancel,Real.exp_zero,Complex.ofReal_one]; -- push cast? adjust
abbrev Acres (t:ℝ)(i:ℕ): Cn:= PowerSeries.C (fee t i)
lemma acres_b (t:ℝ)(i:ℕ): Acres t i* Acres (-t) i=1:= by unfold Acres; rw [← map_mul,fee_mul,map_one]
lemma adjust_clock (h:Law V R H)(he:Regular V)(t:ℝ)(x:Points n)(p:Scan G n): install V n ( squeeze t x ) p= Acres (-t) ( totalG p ) * marking (seats ( replay (H t) ) ) ( tune ( R t ) ( install V ) ) n x p := by rw [ ← town h he,CoinQ ]; change _= _*( Acres t _ * _); rw [ ← mul_assoc,mul_comm (Acres (-t) _) (Acres t _),acres_b,one_mul ]; -- by expand, not rewrite second
end YM.FVA2.O.Score
