import YM.OPE.Short.Unison

/-!
# Actual coefficient and phase bounds at weight zero for the flux stress

Every compact separated shape on the true coupled weak comparison trajectory.
On that path the leading Maxwell-Wick stress kernel predicts the renormalized
identity coefficient and the raw correlations in all phases (this uses the
same finite detector Reader and true Final, not fitting an answer to each
phase). No statement here compares arbitrary output sectors or interpolates
the trajectory to all sufficiently small scales. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Short
open Orbits Orbits.Reader Nesting Nesting.Tree Function Filter Set Table Extraction Spec Climb Pert
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(X:Climb.Scaling S) (hG:G.Simple) (H:Pert.FirstExtension U X)
local notation "Q"=>U.sector.derivatives
local notation "gap"=>fun z=> extra (S:=S) (z:=z)
variable {I:Type}[Fintype I]
local notation "σ"=>exponent I
abbrev source := stressTag (I:=I) U
abbrev target := freeTarget (C:=C) (I:=I)
local notation "stamp" k => (X.r k)^σ
local notation "complexStamp" k => ((↑(stamp k):ℂ):ℂ)
variable {M η:ℝ}(ab:Picture I)(hM:0≤M)(hη:0<η)
local notation "states"=> Viewers U

def meter (x:I→E4) :ℂ := Orbits.moment (Maxwell.freeTable C.labels) x (voices (target (C:=C) ab))

include hG hM hη
lemma shell_budget (h:Services C F S) : ∀ᶠ k in atTop,∀ x∈plate I M η,∀ q:Viewers U,∀o:E4,
    ‖(complexStamp k) * Orbits.moment (spectator U q) (harmonic (X.r k) x o) (voices (source U ab)) - (complexStamp k) * scalar U R (harmonic (X.r k) x o) (source U ab) o‖≤(X.r k)^(1/2:ℝ):=by
     have hr:= Orbits.quantitative_separated U R h (voices (source U ab)) (voices gap) hM hη (M:=M) (ε:=1/2) (by norm_num) 0 (show (0:ℝ)<1 by norm_num)
     have hh: Tendsto X.r atTop (𝓝[>]0):= tendsto_nhdsWithin_iff.mpr ⟨X.drips, Eventually.of_forall X.positive⟩
     let Ψ:=fun k (x:I→E4) q (o:E4)=>formula U R (harmonic (X.r k) x o) o (voices (source U ab)) gapPos (voices gap) 0 q
     filter_upwards [hh.eventually hr] with k he x hx q o
     have hZ:= (he (harmonic _ x o) o gapPos (fitted hη (X.positive k).le x o hx)  (by constructor <;> intro j <;> cases j)).2.2.2 q
     have hu : Ψ k x q o=_ := identity_formula U R X hG (harmonic (X.r k) x o) (source U ab) o q (by apply injective_harmonic X hη x o hx k) -- arg fix; maybe want at x hx
     have hpow: ‖(complexStamp k)‖=(X.r k)^(σ:ℝ):= by rw [Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (X.positive k).le _),← Real.rpow_natCast]
     calc _ = ‖(complexStamp k)‖ * ‖Ψ k x q o‖:=by rw [← mul_sub, norm_mul]; congr 1; rw [hu]
          _ ≤ (X.r k)^(σ:ℝ) * (X.r k)^((↑(0:ℕ):ℝ)+1-weight (degrees (source U ab))-(1/2:ℝ)):= hpow ▸ mul_le_mul_of_nonneg_left hZ (norm_nonneg ((complexStamp k))) -- syntax
          _ = _:=by rw [←Real.rpow_add (X.positive k),stress_weight]; congr 1; ring_nf
where stress_weight: weight (degrees (source U ab))=(↑(exponent I):ℝ):=by unfold weight degrees exponent; change ∑ j:I,(↑(4:ℕ):ℝ)= _; simp; ring

variable (h:Services C F S)
include H h
lemma predicts {ε:ℝ}(hε:0< ε) : ∀ᶠ k in atTop,∀ x∈plate I M η,∀ o:E4,
      ‖(complexStamp k) * scalar U R (harmonic (X.r k) x o) (stressTag U ab) o-meter (C:=C) ab x‖≤ε ∧
       ∀ q:Viewers U, ‖(complexStamp k) * Orbits.moment (spectator U q) (harmonic (X.r k) x o) (voices (stressTag U ab)) - meter (C:=C) ab x‖≤ε:= by
 -- all q including none, both predictions
    have hc:= comparable (ε:=ε/3) U X H ab (K:=plate I M η) (meal I M η) (fun x hx=> plate_conf hη x hx)
    have hh:= shell_budget U R X hG ab hM hη h
    let e:=ε/3; have he:0<e:=by unfold e; positivity
    have h_t: ∀ᶠ k in atTop,(X.r k)^(1/2:ℝ) ≤ e :=by
         have hr:= (Real.continuous_rpow_const (by norm_num : 0 ≤(1/2:ℝ))).continuousAt.tendsto.comp X.drips -- exponent
         exact hr.eventually (p:=(· ≤ e)) (by rw [Real.zero_rpow (by norm_num : (1/2:ℝ)≠0)]; exact ge_mem_nhds he)
    filter_upwards [hc he,hh,h_t] with k h1 h2 h3 x hx o
    let s:=(complexStamp k)
    let y:=harmonic (X.r k) x o
    let v:=stressTag U ab
    let f(q:Viewers U):=Orbits.moment (spectator U q) y (voices v)
    let K':=meter (C:=C) ab x
    let c:=scalar U R y v o
    have hL:‖s * c - K'‖ ≤ 2*e:= by
        calc _ ≤‖s*f none - s*c‖+‖s*f none-K'‖:=(norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add_left (norm_sub_rev ..|>.le) _) -- notation? triangle
             _ ≤ _:= by rw [two_mul]; exact add_le_add ((h2 _ hx none o).trans h3) (h1 _ hx o)
    constructor
    · exact hL.trans (by dsimp only [e] at *; linarith only [he])
    intro q
    apply (norm_sub_le_norm_sub_add_norm_sub (s*f q) (s*c) _).trans ((add_le_add ((h2 x hx q o).trans h3) hL).trans (by dsimp only [e]; ring_nf; first | exact le_rfl | norm_num))
omit hG H h hM in
lemma meter_bound:∃ C':ℝ, 0 ≤ C' ∧ ∀x∈plate I M η,‖meter (C:=C) ab x‖≤C':=by
   let s:= meter (C:=C) ab
   have ht:ContinuousOn s (plate I M η):=((Next.UVStress.smoothDisc (Maxwell.table_smooth C.labels) (Orbits.tags (voices (target (C:=C) ab )) ∘ runNames I)).continuousOn).comp (f:=frame) framed.continuous.continuousOn (fun x hx=> occupancy x (plate_conf hη x hx))
   obtain ⟨c,hc⟩:= (meal I M η).bddAbove_image (f:=norm ∘ s) ht.norm
   exact ⟨max c 1, zero_le_one.trans (le_max_right ..),fun y hy=>(hc (Set.mem_image_of_mem (norm ∘ s) hy)).trans (le_max_left ..)⟩

lemma budget:∃ A:ℝ, 0 ≤ A ∧ ∀ᶠ k in atTop,∀ x∈plate I M η,∀ o:E4,
      ((X).r k)^σ * ‖scalar U R (harmonic ((X).r k) x o) (stressTag U ab) o‖≤A ∧
       ∀ q:Viewers U, ((X).r k)^σ * ‖Orbits.moment (spectator U q) (harmonic ((X).r k) x o) (voices (stressTag U ab))‖≤A :=by
    obtain ⟨d,hd,Hd⟩:=meter_bound (C:=C) ab (M:=M) hη; refine ⟨1+d,by positivity,?_⟩
    have hp(k:ℕ): ‖(complexStamp k)‖=(X.r k)^σ:=by rw [Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (X.positive k).le _)] -- positive via X.positive
    filter_upwards [predicts U R X hG H ab hM hη h (zero_lt_one' ℝ)] with k hk x hx o -- h shadow
    specialize hk x hx o
    rw [←hp k]; simp_rw [← norm_mul]
    refine ⟨?_ ,fun q=>?_⟩
    all_goals apply (norm_le_aux (meter (C:=C) ab x) _) (Hd x hx)
    all_goals first | exact hk.1 | exact hk.2 q
where norm_le_aux (b a:ℂ){d:ℝ}(hb:‖b‖≤d)(hh:‖a-b‖ ≤ 1): ‖a‖ ≤ (1+d):= (congr_arg norm (show a=a-b+b from (sub_add_cancel ..).symm)).trans_le ((norm_add_le ..).trans (add_le_add hh hb))

omit H h hM hη in
lemma unit_piece (i:R.channels 0):R.coef 0 i (sole (0:E4)) (sole (S.unit 0):Labels S (fun _:Unit=>0)) 0=(R.basis 0).repr ⟨S.unit 0,(R.piece_mem .. |>.mpr fun v=> v.elim0)⟩ i :=by
   have hi : S.unit 0 ∈ R.stratum 0:= (R.piece_mem ..).mpr (fun v=> v.elim0)
   exact congr_arg ((R.basis 0).repr · i) (Subtype.ext ((Orbits.Reader.single R ..).trans (R.test_fixes _ _ hi)))

omit H h hM hη in
include X in
lemma first_coef (i:R.channels 0)(x:I→E4)(v:I→S.Tag)(o:E4): R.coef 0 i x (voices v) o = scalar U R x v o * R.coef 0 i (sole (0:E4)) (sole (S.unit 0):Labels S (fun _:Unit=>0)) 0:=by
    let c:=scalar U R x v o; rw [unit_piece U R hG i];
    calc _ = (R.basis 0).repr (c • (⟨S.unit 0,(R.piece_mem .. |>.mpr fun v=>v.elim0)⟩:R.stratum 0)) i:=congr_arg ((R.basis 0).repr · i) (Subtype.ext ((scalarizes U R X hG ..).symm))
         _ = _ := DFunLike.congr_fun ((R.basis 0).repr.map_smul _ _) i -- DFunLike

theorem payment (i:R.channels 0): ∃ A: ℝ,0 ≤ A ∧ ∀ᶠ k in atTop,∀(y:I→E4)(o:E4),WithinRoom ((X).r k) M η y o → ‖R.coef 0 i y (voices (stressTag U ab)) o‖ ≤ A * ((X).r k)^(-(σ:ℝ)) :=by
    obtain ⟨D,hD,hw⟩:=budget U R X hG H ab hM hη h
    let c := R.coef 0 i (sole (0:E4)) (sole (S.unit 0):Labels S (fun _:Unit=>0)) 0
    refine ⟨D * ‖c‖,mul_nonneg hD (norm_nonneg _),?_⟩
    filter_upwards [hw] with k hk y o hy
    obtain ⟨z,hz,rfl⟩:=unframe (X.positive k) hy
    rw [first_coef U R X hG i]
    have ht:= (hk z hz o).1
    let r:ℝ:=X.r k
    change ‖ _ * c‖ ≤ D * ‖c‖ * r^(-(σ:ℝ)); rw [Real.rpow_neg (X.positive k).le, Real.rpow_natCast, norm_mul, ← div_eq_mul_inv]; exact (le_div_iff₀ (pow_pos (X.positive k) _)).mpr ((mul_comm _ (r^σ)).trans_le (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)))
where unframe {r:ℝ}(hp:0 < r){x:I→E4}{o:E4}(hx:WithinRoom r M η x o):∃ z∈plate I M η,harmonic r z o=x:=by
        refine ⟨fun i=>r⁻¹ • (x i-o),⟨?_, ?_⟩,funext fun i=>by unfold harmonic; erw [smul_inv_smul₀ hp.ne' (x i-o),sub_add_cancel]⟩
        · intro i; nth_rw 1 [sub_zero,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hp).le]; rw [mul_one,inv_mul_le_iff₀ hp,mul_comm]; apply hx.span
        intro i j hij; rw [mul_one,← smul_sub]; change η ≤ ‖r⁻¹ • (x i-o-(x j-o))‖; rw [show x i-o-(x j-o)=x i-x j from (sub_sub_sub_cancel_right ..),norm_smul,Real.norm_of_nonneg (inv_pos.mpr hp).le, le_inv_mul_iff₀ hp,mul_comm]; exact hx.spaced i j hij
end YM.OPE.Short
