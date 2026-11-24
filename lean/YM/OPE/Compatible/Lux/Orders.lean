import YM.OPE.Compatible.Lux.Satellite
/-!
# Sharp Scores (assuming matching directions) of direct field coordinates and of whole parent compression error in every Burst
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Set Filter Table MeasureTheory Cov Display Survey Trace
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)
   {I J V:Type}[Fintype J][Fintype I][PartialOrder I][OrderBot I]
variable (D:Origin I){Q:Finset I}(A:Allot C)(hL:Lanes (F:=F) U.sector.derivatives)(hs:Services C F S)
variable {ψ:Filter V} [ψ.NeBot]{T: V→ℝ}{s:V→I→ℝ}{η M c:ℝ} {x:V→I→E4}(H: Burst D Q ψ T s)
variable (hx:∀ᶠ i in ψ,Ridge (s i) η M D Q (away (x i) (x i ⊥)))(hη:0<η)(hM:0 ≤ M)
variable (p:brim D Q→ S.Tag)(y: V→J→ E4)(q:J→ S.Tag)(v:V→Viewers U)
-- norm recovery from moving phase
omit [ψ.NeBot] in
lemma glance_go (ht:Tendsto T ψ atTop){f:V→Display.Round U}(h:∀ r:V→Viewers U, Score ψ T (fun i=> glance U (r i) (f i))) : Score ψ T f:=by
    have hp i:∃ r:Viewers U,‖f i‖ ≤ 2*‖glance U r (f i)‖ :=by
        by_cases he : ‖f i‖=0; · refine ⟨none,?_⟩; rw [he]; positivity
        by_contra! hg
        have hv : ‖f i‖≤ ‖f i‖/2:= (glance_contract U (by positivity)).2 (fun r=>by linarith only [hg r]); linarith [lt_of_le_of_ne (norm_nonneg (f i)) (Ne.symm he)]
    choose a ha using hp
    let A i := glance U (a i) (f i); refine ((Score.steady (2:ℝ) ht).product ((h a).liftp (w:=fun i=>‖A i‖) (Eventually.of_forall fun _=> by simp [A]))).under ?_; exact Eventually.of_forall ha
local notation "k"=> brim D Q
set_option quotPrecheck false
local notation "o"=> fun i=> x i ⊥
local notation "Y" => fun i=> picked (brim D Q) (x i)
local notation "B!"=>fun i=>s i ⊥
local notation "Z"=> fun d i=> costed D Q d (Sigma.fst∘p) (s i)
include H A hL hs hx hη hM
omit [ψ.NeBot] in
lemma solid_beam (w:Tones U): PaidWeight ψ T (Z w.fst) (fun i=> beam U w (B! i) (Y i) p (o i)):=by
    let n:=w.fst; have ht := (H.fresh _ hη).fade _ (Burst.crown D H).base; refine (earns_lens U D A hL hs H hx hη hM p w).alter ?_; filter_upwards [ht.eventually self_mem_nhdsWithin,(ht.mono_right nhdsWithin_le_nhds).eventually (ge_mem_nhds (Signal.period_pos (supplies S) n))] with i hi hx; rw [beam, Signal.lit _ _ hi hx, Complex.ofReal_one,one_mul]
lemma solid_price (d:ℕ)(hc:0<c)(hf:∀ᶠ i in ψ, ClearOf (x i ⊥) (y i) c) : PaidWeight ψ T (Z (d+1)) (fun i=> drift U d (B! i) (Y i) p (o i) (y i) q):=by
   have he := (clear_awayU D H hx hη y hf hc).2; have ht:= (H.fresh _ hη).fade _ (Burst.crown D H).base; have hs0:= ht.eventually self_mem_nhdsWithin; have hw:= (ht.mono_right nhdsWithin_le_nhds).eventually (ge_mem_nhds (Signal.period_pos (supplies S) d)); have hg:∀ᶠ i in ψ,0 ≤ Z (d+1) i:= (cost_pos D H p (d+1)).mono fun _ h=>h.le
   apply (PaidWeight.ascaled (X:=Display.Round U) hg).2; apply glance_go U (Burst.life D H); intro r; refine ((PaidWeight.ascaled hg).1 (earns_screen U D A hL hs H hx hη hM p y q r d hc hf)).congr ?_
   filter_upwards [he,hs0,hw] with i he hi hb; rw [map_smul,drift_reveals U _ _ _ _ _ _ _ he.1 he.2,trunc_ray U d hi hb]
end YM.OPE.Arboreal
