import YM.MS.SpaceOut.Vault
/-!
# Post contour and population households. Proves thermal line budget assumptions of orbit theorem.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.SpaceOut
open Set Filter Function Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Vista
open scoped Topology ContDiff Interval
variable {G:Gauge}{I:Type}{S:Scale I}{P:Belt I}{ M:Visa I}{L:I→Side}{K:Planet G I}
local notation "Ψ"=>After M L
local notation "Χ"=>lampV G L
local notation "Ω"=> uniform G I
lemma νx (i:( After M L ).time): tickA L i.1 ≤ τ ( tstart i ) := by rw [ ← τ_h ]; exact τ_m ( afterT i )
def future (P:After M L|>.time) := τ ( tstart P )
lemma ψtwo (i:(Ψ).time): 2≤ (Ψ).price.length i:= south_l ..
lemma ψ_time (i:(Ψ).time) : 0<future i:= ( (Ψ).price.pos i ) |>.trans_le ( νx _ ) -- defeq Progress.
def Outside (L:I→Side)(M:Visa I): Scale (After M L|>.time):= ⟨ future,ψ_time,(After M L).price.basic, (After M L).price.one_le⟩
lemma spare (i:(Ψ).time): ( Outside L M ).length i=future i:=rfl
lemma ψ_l (i:(Ψ).time) : 1≤ future i:= ( δ_L .. )|>.trans (νx i)
lemma ψ_fn (i:(Ψ).time): future i=Vista.lamp (tstart i):= Eq.symm (max_eq_right (ψ_l i))
lemma spiral (x:(Ψ).time): (Ψ).price.length x/(Outside L M).length x≤ Tail M L x:= by
    let v:= tickA L x.1; let ρ:= tstart x-until0 L x.1; have hr:0≤ρ:= sub_nonneg.mpr ( afterT x ); let G:=exp ρ; obtain hg:= Vista.boost x; obtain he:= ψ_time x; have hx:= δ_p L x.1; rw [ afterR ]; change v/future x ≤ _; apply le_trans (b:=exp (-ρ));
    · rw [div_le_iff₀ he, ψ_fn, exp_neg]; exact ( (le_inv_mul_iff₀ (exp_pos _ ) ).2 ( by rwa [mul_comm (exp _)] ) ) -- name
    apply Real.exp_monotone; unfold eps_gain; change -ρ≤ -(1/2:ℝ)*ρ; linarith
lemma star (i:BH G): 0≤ 2-wfield i:= by unfold wfield dim; cases i.1.2 <;> simp -- unused p.
lemma trackζ (K:Planet G I)(h:Glow K) : PerK (plug (J:=P.slot) (zoom K)):= fun i j k p q hp=> by simp_rw [ show ∀ p:QP,plug (zoom K) i j k p=( (exp ( tstart i ):ℝ):ℂ)* K i.1 (τ (tstart i)) j k p from fun p=> rfl ]; exact congr_arg _ ( h.proper _ _ |>.pin j k hp ) -- lambda app
lemma origin_Time (i:I)(t:ℝ): zoom (uniform G I) i t=dope ( Origin G (τ t) ):= by funext a b p; simp only [ τ, zoom,uniform, LaceL, dope,Origin, Pi.smul_apply,smul_eq_mul, show 1+(exp t-1)=exp t from (by abel) ]; ring
lemma Stageβ (i j:BH G): Line (Ψ).price located (fun t: (Ψ).time=> plug (zoom ( lampV G L )) t i j) (fun t=> (Ψ).price.length t ^ ( (4:ℤ)-wfield i-wfield j ) * Tail M L t ):= by
    let S:=(Ψ).price; let T:=Outside L M; let v:ℤ:=4-wfield i-wfield j; have hv:0≤v:= by unfold v; obtain he:=star i; obtain hx:=star j; omega
    let f(t: (Ψ).time):= plug (zoom Ω) t i j; have he: Frost T ( fun t=> dope ( Origin G ( future t ) ) ) 1:= by apply d_frost ( originΦ ( u:=fun i:(Ψ).time=>future i ) (fun i=> by change future i=max (1:ℝ) (future i); rw [max_eq_right (ψ_l i)]) (fun i=> (ψ_time i|>.le))); exact ψ_l
    have hF: Line T located f (fun t=>T.length t^v.toNat):= by
       obtain hx:= he i j; unfold f; simp_rw [ show ∀ t:(Ψ).time, plug (zoom Ω) t= dope ( Origin G (future t) ) from fun _=> origin_Time .. ]; convert hx using 1; funext t; change T.length t^ v.toNat = T.length t ^ v * 1; rw [ mul_one,← Int.toNat_of_nonneg hv, zpow_natCast ]; simp [hv]; -- may rw at v lhs
    rw [show (fun t: (Ψ).time=> plug (zoom ( lampV G L )) t i j)= masker S T f from ?mask ]; swap; · funext t p; unfold f zoom masker; change ((( exp (tstart t):ℝ):ℂ)* (( SpaceOut.veil ( S.length t ) ( T.length t ) p:ℂ )*_))=_; exact mul_left_comm ..
    refine (crest (S:=(After M L).price) (T:=T) ψtwo v.toNat νx (fun _=> rfl) hF).monotone (fun i'=>?_); have he(p): S.length p ^ v.toNat=S.length p ^ v:= by nth_rw 2 [← Int.toNat_of_nonneg hv]; rfl
    change S.length i' ^ v.toNat * _≤ S.length i' ^ v * _; rw [he]; exact mul_le_mul_of_nonneg_left (spiral i') (length_p ..) -- cast mismatch
lemma Doors (G:Gauge)(V:Visa I)(L:I→Side): Budget V L (lampV G L) (uniform G I):= by
    let X:=After V L; let T:=Mid V L; obtain hP:= step_j G V L; obtain H:= health G L; refine ⟨ H, healthy .., fun b=> ?_, fun b=> forkη (b:=b) soonM.large ( Stageβ (G:=G) (M:=V) ) ( trackζ _ H ), origin_ge _ (fun i=> i.2.property ) (fun i=>rfl),hP ⟩; rw [ χ_same hP ]; exact origin_ge T (fun i=> midT i |>.1 ) (fun i=> rfl ) b
end YM.MS.SpaceOut
