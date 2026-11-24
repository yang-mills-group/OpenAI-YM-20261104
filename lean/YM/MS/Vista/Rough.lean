import YM.MS.Vista.Portal
/-!
# Shifts in affine spaces: toll extension under a temporary cost. Never global length-loss.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Filter Function Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open scoped Topology ContDiff Interval
variable {I E F G:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup G][NormedSpace ℝ G]
   {S:Scale I}{P:Cost I E}{Q:Cost I F}{f:I→ E→ G}{L:F→L[ℝ] E}{x:F}{p:E}{s t:I→ℝ}{D:I→ Set F}
lemma tilted (A:F→L[ℝ] E)(p:E) {g:I→ E→ℝ}(hf:Costs P S f g)(h:∀ i,MapsTo (fun x=>A x +p) (Q.zone i) (P.zone i))(hu:Q.Le (fun i x=>P.cheap i ( A x+p )) (fun _ _=>1)): Costs Q S (fun i x=> f i ( A x+p )) (fun i x=>g i ( A x+p)):= by
    let L:= fun i: I=> (fun x:F=> A x+p); let F(s:I)(x:E):= f s ( x+p ); have he i: ContDiff ℝ ∞ ( F i ):=(hf.smooth i).comp (f:=fun x:E=> x+p) (by fun_prop); refine ⟨fun i=> (he i).comp (A.contDiff),fun j=>?_⟩; have hv:= Cost.Le.pull ( T:=P) (S:=Q) (hf.quoted j) (φ:=id) ( ψ:=L ) h hu (Cost.nn_of_le (hf.quoted j) fun i p _=> norm_nonneg _);
    obtain hz:= Cost.Le.const_mul hv (‖A‖^j) (by positivity) (Cost.nn_of_le hv (fun i p _=> norm_nonneg _)); apply Cost.Le.left hz; intro i pK hP; change ‖iteratedFDeriv ℝ j (F i∘ A) pK‖ ≤ ‖A‖^j* ‖iteratedFDeriv ℝ j (f i) (A pK+p)‖; rw [A.iteratedFDeriv_comp_right (f:= F i) (he i) _ (by exact_mod_cast le_top)]; rw [mul_comm, ← iteratedFDeriv_comp_add_right ]; convert ContinuousMultilinearMap.norm_compContinuousLinearMap_le (iteratedFDeriv ℝ j ( F i ) (A pK)) (fun _=>A) using 1; simp [ F ] -- wrong arg order
-- window.
def Slice (S:Scale I)(D:I→Set F) : Cost I F:={S.full with zone:= D, one_le:=fun i p _=> ( S.full.one_le i p trivial ) }
abbrev wideCost (S:Scale I)(D:I→Set F) (x:I→ℝ)(hp:∀ i,1≤x i): Cost I F:= ⟨ D,fun i p=> x i*S.full.cheap i p, fun i p _=> one_le_mul_of_one_le_of_one_le ( hp i ) (S.full.one_le i p trivial)⟩
-- λ Rough.We only pay at j.Of ST. `absorb`
variable {f g:I→F→ℂ}{A: I→ℝ}
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma cloveR (v:I→ℝ)(h:∀ i,1≤v i)(hf:Costs ( wideCost S D v h ) S f (fun i _=>s i))(j:ℕ): ∃ k:ℕ,(Slice S D).Part S f (fun i _=> s i*v i^k ) j:= by
    obtain ⟨U,hU,k,hk⟩:= hf.quoted j; refine ⟨ k,U,hU,k,fun i p hx=>(hk i p hx)|>.trans_eq ?_ ⟩; simp only [ Slice ]; ring
lemma shoulder (v:I→ℝ)(h:∀ i,1≤v i)(hf:Costs (wideCost S D v h) S f (fun i _=>s i))(he:∀ j:ℕ, Costs ( Slice S D ) S g (fun i _=> t i /v i^j)): Costs (Slice S D) S (fun i p=> g i p * f i p) (fun i _=>t i*s i):= by
   refine ⟨fun i=>( he 0|>.smooth i ).mul ( hf.smooth i), fun j=> ?_ ⟩; choose r hr using (cloveR v h hf); let u:= (Finset.Iic j).sup r; let B:= ContinuousLinearMap.mul ℝ ℂ; have H:∀ i,(t i/v i^u)*(s i * v i^u)=t i*s i:= fun i=>by have hs :0<v i:= lt_of_lt_of_le zero_lt_one ( h i ); field_simp
   convert Cost.Part.bilinear ( S:=S ) B (he u|>.smooth) hf.smooth (fun k hk=> he u |>.quoted k ) (j:=j) (g':=(fun i _=>s i*v i^u)) ?_ using 1; rfl; · exact funext fun i=> funext fun _=> (H i).symm
   intro k hk; apply Cost.Part.adjust ( hr k ) (Cost.of_le ?_); intro i p hx; obtain hv:= hf.nonneg i p hx; gcongr; · exact h i
   exact Finset.le_sup (s:=Finset.Iic j) (f:=r) ( Finset.mem_Iic.mpr hk )
lemma blendC {B C:I→Set F} (h:∀ i p,p∈ B i ∨ p∈ C i)(hg:Costs (Slice S B) S f (fun i _=>s i))(hf:Costs (Slice S C) S f (fun i _=>s i))(ht:nn s): Bound S f s:= by
    refine ⟨ hf.smooth,fun j=>?_⟩; obtain ⟨U,hU,v,hV⟩:= hg.quoted j; obtain ⟨W,hW,k,hK⟩:= hf.quoted j; refine ⟨ U+W,add_pos hU hW,v+k,fun i p hp=>?_⟩; have hx:= S.full.one_le i p hp; have hr:=ht i; have hm:= S.pos i; rcases h i p with h|h; apply le_trans ( hV i p h ); dsimp only [Slice]; gcongr; linarith; omega; apply le_trans ( hK i p h ); dsimp only [Slice]; gcongr; linarith; omega -- indent fix `h|h;`
end YM.MS.Vista
