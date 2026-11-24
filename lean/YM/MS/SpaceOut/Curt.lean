import YM.MS.SpaceOut.Hop
/-!
# Choosing extension in final sector, still agrees exactly with the heat lines on finite period.Factor.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.SpaceOut
open Set Filter Function Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Vista Orbit.LogReal
open scoped Topology ContDiff Interval
variable {G:Gauge}{ W I:Type}{L:I→Side}{S:Visa I}{K: Planet G I}{n:Side}
def veil (n r:ℝ)(x:QP): ℝ:= 1 - Real.smoothTransition ( r/n-1 ) * rim n x
lemma before_B (n r:ℝ)(h:0<n)(hx:r≤n): veil n r=1:= by ext x; unfold SpaceOut.veil; rw [Real.smoothTransition.zero_of_nonpos (by rw [sub_nonpos,div_le_one h]; exact hx), zero_mul,sub_zero ]; rfl
lemma after_B (n r:ℝ)(h:0<n)(hx: 2*n ≤ r): veil n r=(fun q=>1-rim n q):= by ext x; unfold SpaceOut.veil; rw [Real.smoothTransition.one_of_one_le (by rw [ le_sub_iff_add_le,le_div_iff₀ h]; linarith [hx] ), one_mul ] -- norm cast?
lemma smoothB {q:ℝ}(hz:2≤q): ContDiff ℝ ∞ (uncurry (veil q)):= by unfold SpaceOut.veil uncurry; refine contDiff_const.sub (((smoothTransition.contDiff).comp ( ( contDiff_fst.div_const _ ).sub contDiff_const )).mul ((rim_s hz).comp contDiff_snd))
abbrev south (n:Side):ℝ:=(periodN n).val
lemma south_l (n:Side): 2≤ south n:= by unfold south; rw [cap_val]; exact_mod_cast Nat.le_mul_of_pos_right 2 n.property
lemma south_h (n:Side):0<south n:= δ_p (fun (_:Unit)=>n) ()
lemma rim_lo (p: Orbit.Zone n)(hp:p≠0) : rim (south n) (Coord p)=0:= by
   rw [rim_Q (south_l n) (stretchP ( entered p )) ]; apply west_off (south_h _|>.le); rw [absstep]; change _ < south n * ( ( tier / south n ) *_); rw [← mul_assoc (south n), div_eq_mul_inv,mul_left_comm (south n) tier,mul_inv_cancel₀ (south_h n|>.ne'),mul_one]; obtain ht: (1:ℝ) ≤ pdist p:=(by exact_mod_cast (discr p hp)); unfold tier wide; nlinarith [Real.pi_pos]
lemma coach_zero (G:Gauge)(i j:BH G)(t:ℝ) : Cpu G t i j 0=0:= by unfold Cpu LegsK Landau.choir; split; swap; rfl; rcases i with ⟨⟨_|i,_|_⟩,u⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,v⟩ <;> simp [ L0,wave, theta, delta,Momentum.sq,precision ]
-- normalize site line.W. Keep covariance phase.Hp.
abbrev lampV (G:Gauge)(L:I→ Side) : Planet G I:= fun i t s j q=> (veil (south (L i)) t q:ℂ)*LaceL G t s j q
lemma health (G:Gauge)(L:I→ Side): Glow (lampV G L):= by
   let K:= lampV G L; constructor; · exact fun i j k=> (Complex.ofRealCLM.contDiff.comp (smoothB (south_l ( L i )))).mul ( (flexD (main_f G)) j k )
   intro i t; obtain ⟨h,hT,he,hU⟩:= foe G t; let d(x:QP):=(veil (south ( L i )) t x:ℂ ); have hz : pinQ d:= by intro p q H; unfold d SpaceOut.veil; rw [ rim_per ( south_l _ ) H ];
   have hv(p:QP):d (-p)=d p:= by unfold d SpaceOut.veil; rw [even_Q ( south_l _ )]
   refine ⟨ fun i j _ _ H=> congr_arg₂ (· * ·) (hz H) (h i j H),?_, fun i j q hh=> he _ _ _ ( right_ne_zero_of_mul hh ),?_ ⟩; all_goals intro i j p'; change d _*_ = _
   · rw [hv,hT]; exact mul_left_comm ..
   rw [hv,hU,← mul_assoc ]
lemma seen (G:Gauge)(L:I→Side)(i:I)(p: Orbit.Zone ( L i ))(u v: BH G)(t:ℝ): lampV G L i t u v (Coord p)=LaceL G t u v ( Coord p ):= by
   unfold lampV; by_cases hx:p=0; · subst p; rw [ξ_zero]; unfold LaceL dope; rw [coach_zero]; ring
   rw [SpaceOut.veil, rim_lo p hx,mul_zero,sub_zero,Complex.ofReal_one,one_mul]
lemma conf (G:Gauge)(L:I→ Side)(i:I)(t:ℝ): mat (dimT L i) ( lampV G L i t )= mat ( dimT L i ) ( LaceL G t ):= by ext p q; unfold Orbit.mat EdgeV; simp_rw [seen]
lemma traveller (G:Gauge)(L:I→Side)(b:Bool)(i:I): zoneP L b (lampV G L) i=normal G (dimT L i) b:= by funext t; exact congr_arg (( iota G _ ).imageV b) ( conf G L i t )
lemma no_diff (G:Gauge)(L:I→Side)(t:ℝ)(i:I)(he:t ≤ tickA L i): lampV G L i t=LaceL G t:= by ext x y p; unfold lampV; rw [ SpaceOut.before_B (south _ ) t ( δ_p L i ) he ]; simp
lemma step_j (G:Gauge)(S:Visa I)(L:I→Side): stepOne S L (lampV G L) ( Orbit.uniform G I ):= funext fun (p:(Mid S L).time)=> by change _ • lampV G L p.1 (Vista.τ (tstart p))=_ ; rw [ no_diff ]; rfl; exact τ_m (midT p|>.2 )|>.trans_eq (τ_h ..)
end YM.MS.SpaceOut
