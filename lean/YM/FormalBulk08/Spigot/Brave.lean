import YM.FormalBulk08.Spigot.Slates
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spigot
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City Wine Flat Glide Bank Chapel Rift Kemp Dawn MeasureTheory
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {I:Type}{G:Gauge}{n:Side}{r t u e E D:ℕ}{A B C σ η:ℝ}
open Grail Precision Work.F03 Pose Tensor
open Planned.PrimaryIntegral295 Place Carrier
open scoped Matrix.Norms.Frobenius

variable {M:Cabin D I G r}

def canon (M:Cabin D I G r)(p:Studio D)(x:Link G n):=∑' i,M.pulse i p * spring (M.atoms i) x
lemma canon_germ (h:Energy M u σ A)(hs:0<σ)(p:Studio D)(n:Side): AnalyticAt ℝ (canon M p (n:=n)) 0 ∧ ∀ t (x : Fin t→Link G n), HasSum (fun i=> (M.pulse i p)*Tensor.coeff (spring (M.atoms i)) t 0 x) (Tensor.coeff (canon M p) t 0 x):= by
   obtain ⟨R,hR,H⟩:=term_vault G hs
   choose f hf hh hx using fun i=> H r (M.atoms i) n 0; let S i:=(M.pulse i p:ℂ) • (f i); let B i:= M.pulse i p • (spring (M.atoms i) (n:=n)); let D i := (M.atoms i).budget σ * ‖M.pulse i p‖ * Work.F02.slotConst G^r
   have hg: Summable D:= (deposits h hs.le p).2.1.mul_right _
   have he i: ContDiff ℂ ω (S i):= (hf i).const_smul (M.pulse i p:ℂ)
   have hp i x (hv:x∈ Metric.ball 0 R): ‖S i x‖ ≤ D i:= by unfold S D; rw [Pi.smul_apply,norm_smul,Complex.norm_real]; exact (mul_le_mul_of_nonneg_left (hh i _ hv) (norm_nonneg _)).trans_eq (by ring)
   have hz (i:I) : S i ∘ axes=Complex.ofRealCLM ∘ B i:= by
      ext1 x; unfold S B; simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul,Complex.ofRealCLM_apply,Complex.ofReal_mul]; congr 1; exact congr_fun (hx i) x
   let K := canon M p (n:=n); have hZ : (fun x=>∑' i,S i x)∘ axes=Complex.ofRealCLM ∘ K:= by
       funext x; change (∑' i,S i (axes x)) = ((∑' i,B i x:ℝ):ℂ); simp_rw [show ∀ i,S i (axes x)=↑(B i x) from fun i=> congr_fun (hz i) x]; rw [Complex.ofReal_tsum]
   refine ⟨earth_cont hZ (Work.F02.analytic_series _ hR (fun i=> (he i).differentiable (by simp)) hg hp),fun t x=>?_⟩
   have hQ:=mixtape B S hR hg he hp hz t (axes ∘ x); simp_rw [note_real] at hQ; let b i:= M.pulse i p * Tensor.coeff (spring (M.atoms i)) t 0 x; have hC: HasSum (fun i=> (b i:ℂ)) (↑(Tensor.coeff K t 0 x)):= by
       simp_rw [B, Tensor.coeff_smul (M.pulse _ p) ((spike _).of_le (show (t:WithTop ℕ∞)≤ω from le_top))] at hQ; exact hQ
   exact Complex.reCLM.hasSum hC
lemma canon_jet (o:Loc G 1)(h:Energy M u σ A)(hs:0<σ)(p:Studio D)(n:Side)(j:ℕ): sieve n (candle M p j)=Broc.beam (canon M p) j:= funext fun v=> (candle_tor o h hs p v).trans ((canon_germ h hs p n).2 j (dotI ∘ v)).tsum_eq
lemma trace_bill {X:Type}[Fintype X](f:Jets.Rays X→ℝ)(t:ℕ)(x): traceP x (PowerSeries.coeff t (paste f))= Tensor.coeff f t 0 (fun _=>x):= by rw [trace_paste];rfl
lemma canon_gain (h:Energy M u σ A)(hs:0<σ)(p:Studio D)(x: Link G n)(t:ℕ):HasSum (fun i=> M.pulse i p * traceP x (PowerSeries.coeff t (paste (spring (M.atoms i))))) (traceP x (PowerSeries.coeff t (paste (canon M p)))):= by
    simp_rw [trace_bill]; exact (canon_germ h hs p n).2 t fun _=>x
lemma canon_spring (o:Loc G 1)(h:Energy M u σ A)(hs:0<σ)(p:Studio D)(n:Side)(j)(he:j<r): PowerSeries.coeff j (paste (canon M p (n:=n)))=0:=by rw [←Broc.beam_price,←canon_jet o h hs,candle_low M _ _ he,sieve_zero,map_zero]

def cradle (e:ℕ)(M:Cabin D I G r)(p:Studio D)(n:Side): Pap (wire G n):= X^e* afterX (paste (canon M p (n:=n))) r
lemma cradle_civic (o:Loc G 1)(h:Energy M u σ A)(hs:0<σ)(n:Side)(e:ℕ)(p:Studio D): Rite (cradle e M p n) (cradle e M p n) 1 0:= by
   have H:=(canon_germ h hs p n).1; intro X1 inst v w k hv hw hV hW _ _ hz
   let f:Link G n→ℝ:= canon M p
   have ht : f ∘ v =ᶠ[𝓝 0] f ∘ w:= hz.mono fun b hb=> by
        refine tsum_congr (α:=ℝ) (f:=fun i=>M.pulse i p*spring (M.atoms i) (v b)) (g:=fun i=>M.pulse i p*spring (M.atoms i) (w b)) ?_; intro i; apply congr_arg (M.pulse i p * ·); unfold spring; rw [hb,pull_id]; simp only [Atom.unmasked,Work.F05.slot_gauge]; exact Eq.symm (h.actual i _ _)
   let a:= cradle e M p n; have HZ : X^r*a=X^e*paste f:= by unfold a;rw [cradle,mul_left_comm, after_rope _ _ (canon_spring o h hs p n)]
   apply mul_left_cancel₀ (pow_ne_zero r PowerSeries.X_ne_zero); calc
      X^r * roam ℝ (motor v) a = roam ℝ (motor v) (X^r*a):= by rw [map_mul,map_pow,show roam ℝ _ X=X from change_X _]
      _ = roam ℝ (motor w) (X^r*a) := by rw [HZ,map_mul,map_mul,map_pow,map_pow,show roam ℝ (motor v) X=X from change_X _,show roam ℝ _ X=X from change_X _,← paste_steps _ v H.contDiffAt (hV.of_le le_top) hv,← paste_steps _ w H.contDiffAt (hW.of_le le_top) hw,paste_replace ht]
      _ = X^r * roam ℝ (motor w) a := by rw [map_mul,map_pow, show roam ℝ _ X=X from change_X _]
end YM.FormalBulk08.Spigot
