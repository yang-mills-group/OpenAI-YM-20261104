import YM.FVA2.O.Enh.Twigs
/-!
# Uniform geometry on the inner and large exterior test

`squeeze (-t)` means stretch by T=exp(t). Prove the large-distance estimates
on scale T of the separation of the two groups, uniformly (exterior compact profiles
with separation from origin; no discrete positions, no period).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Enh
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo O.Seam
variable {G: Gauge}{I:Type}{n m d:ℕ}{K:Set ( Points n )}{J:Set ( Points m )}{t:ℝ} -- use two
variable { z:I→ Points m }{P:Geo I}
abbrev Stretch (P:Geo I)(z:I→ Points m): I→ Points m:= fun i=> squeeze (- P.θ i ) ( z i )
lemma norm_g (f:Points m)(t:ℝ)(j:Fin m): Theater.out ( squeeze (-t) f j )= Real.exp t • Theater.out (f j):= by unfold squeeze; simp only [neg_neg, PiLp.smul_apply,map_smul]
lemma norm_t {p:I} (i:Fin m): ‖orange (Stretch P z) i p‖= roots P p* ‖orange z i p‖:= by simp only [orange,Stretch,norm_g,norm_smul]; rw [norm_of_nonneg (exp_pos _|>.le)]
lemma norm_two {p:I}(i j:Fin m): ‖(orange (Stretch P z) i-orange (Stretch P z) j) p‖= roots P p* ‖(orange z i-orange z j) p‖:= by simp only [Pi.sub_apply,orange,Stretch, norm_g,← smul_sub,norm_smul,norm_of_nonneg (exp_pos _|>.le) ]
lemma fixed_J (he: IsCompact J)(hx:∀ i,z i∈J)(u:Fin m): Cool.Fixed ( orange z u ):= by obtain ⟨C,hC,h⟩:= Legs J he u; exact ⟨ C,hC,fun i=> h _ ( hx i ) ⟩
lemma bounded_J (he:IsCompact J)(hx:∀ i,z i∈J)(u v: Fin m): Cool.Fixed ( orange z u-orange z v ):= by
    obtain ⟨C,hC,h⟩:= fixed_J he hx u; obtain ⟨D,hD,hT⟩:= fixed_J he hx v; exact ⟨ C+D,add_pos hC hD,fun i=> ( norm_sub_le .. ).trans ( add_le_add ( h i ) ( hT i ) )⟩
lemma ZoneJ (he:IsCompact J)(hv:J⊆ conf m)(hx:∀ i, z i∈J): Rake.Mesh (flatten P) ( orange z ):= by
    intro i j hp; obtain ⟨C,hC,h⟩:=storyH he hv i j hp; obtain ⟨D,hD,hE⟩:= bounded_J he hx i j; have hh(i:I):roots (flatten P) i=1:=Real.exp_zero; refine ⟨ ⟨ D,hD,fun i=>( hE i ).trans_eq (by rw [hh,mul_one])⟩,C,hC, fun p=>?_⟩; rw [hh,mul_one]; exact h _ ( hx p )
lemma row_Ω (h: IsCompact J)(he:J⊆ Outside m)(hp:∀ i,z i∈J)(u:Fin m): CoverSep P ( orange ( Stretch P z ) u ):= by
    obtain ⟨ C,hC,hp'⟩:= fixed_J h hp u; obtain ⟨D,hD,h⟩:= storyY h he u; refine ⟨ ⟨ C,hC,fun i=>?_⟩, D,hD,fun i=>?_⟩; · rw [ norm_t,mul_comm C ]; exact mul_le_mul_of_nonneg_left ( hp' i ) (exp_pos _|>.le)
    rw [norm_t,mul_comm D ]; exact mul_le_mul_of_nonneg_left ( h _ ( hp i ) ) (exp_pos _|>.le)
lemma Zone_Ω (h:IsCompact J)(hp:J⊆conf m)(hv:∀ i,z i∈J): Rake.Mesh P ( orange ( Stretch P z )):= by
    intro i j hq; obtain ⟨C,hC,h⟩:= ZoneJ (P:=P) h hp hv i j hq|>.full; obtain ⟨D,hD,hT⟩:= ZoneJ (P:=P) (J:=J) (by assumption) hp hv i j hq|>.floor; refine ⟨ ⟨ C,hC,fun p=>?_⟩,D,hD, fun p=>?_⟩
    · rw [ norm_two,mul_comm C ]; exact mul_le_mul_of_nonneg_left ( (h p).trans_eq (by change _*Real.exp 0=_; simp) ) (exp_pos _|>.le)
    rw [ norm_two,mul_comm D ]; refine mul_le_mul_of_nonneg_left ?_ (exp_pos _|>.le); specialize hT p; rw [ show roots ( flatten P ) p=1 from Real.exp_zero,mul_one ] at hT; exact hT
-- independent threshold for ALL alphabet positions ($L*1≤P^θ$). existence growth when finite. Provide cross for any P above
lemma Cross (hP:IsCompact K)(hJ:IsCompact J)(he:J⊆Outside m): ∀ᶠ b:ℝ in atTop,∀ {I':Type} {P:Geo I'}, (∀ i,b≤P.θ i) → ∀ (x:I'→ Points n)(z:I'→ Points m), (∀ i,x i∈ K)→ (∀ i,z i∈J)→∀ (i:Fin n)(j:Fin m), CoverSep P ( orange ( Stretch P z ) j-orange x i ):= by
    have hp(i:Fin n)(j:Fin m): ∀ᶠ b:ℝ in atTop,∀ {I':Type}{P:Geo I'},( ∀ i,b ≤ P.θ i )→∀ (x:I'→ Points n)(z:I'→ Points m),( ∀ i,x i∈K )→(∀ i,z i∈J)→ CoverSep P ( orange ( Stretch P z ) j-orange x i ):= by
        obtain ⟨D,hD,h⟩:= storyY hJ he j; obtain ⟨C,hC,hK⟩:= Legs K hP i; have he:= Filter.Tendsto.const_mul_atTop (show 0<D/2 from by linarith) (Real.tendsto_exp_atTop); filter_upwards [he.eventually (eventually_ge_atTop C)] with b hb;
        intro I' P hv x z hX hz; obtain ⟨T,hT,hL⟩:= fixed_J hJ hz j; refine ⟨ ⟨ T+C, add_pos hT hC,fun p=>?_ ⟩, D/2,(by linarith),fun p=>?_⟩
        · let f:= orange ( Stretch P z ) j p; let y:= orange x i p; change ‖f-y‖ ≤ _; apply ( norm_sub_le f y ).trans; have hR: 1≤ roots P p:= Real.one_le_exp ( P.room _ ); unfold f; rw [ norm_t,add_mul, mul_comm ( roots _ _ ) ]; exact add_le_add ( mul_le_mul_of_nonneg_right (hL p) (zero_le_one.trans hR) ) (( hK _ (hX p) ).trans ( le_mul_of_one_le_right hC.le hR ))
        let f:=orange ( Stretch P z ) j p; let y:=orange x i p; have hD': ‖y‖ ≤ D/2 * roots P p:= ( hK _ ( hX p ) ).trans ( ( show C≤ D/2*Real.exp b from hb ).trans ( mul_le_mul_of_nonneg_left ( Real.exp_monotone ( hv p )) ( by linarith ) )); change _≤ ‖f-y‖; have hu:= norm_sub_norm_le f y; apply le_trans _ hu; have hR:‖f‖≥D*roots P p:= by unfold f; rw [ norm_t,mul_comm D ]; exact mul_le_mul_of_nonneg_left ( h _ ( hz p ) ) (exp_pos _|>.le)
        linarith
    exact ((( eventually_all ).mpr fun i=> eventually_all.mpr ( hp i ) )).mono fun b H I' P ht x z hx hz i j=> H i j ht x z hx hz
end YM.FVA2.O.Enh
