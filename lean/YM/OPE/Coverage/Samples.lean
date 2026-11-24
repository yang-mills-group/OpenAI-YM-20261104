import YM.OPE.Coverage.Store
import YM.OPE.Coverage.Beads
import YM.Extra.WEAK_SCALING_ACTLAW.Jets

/-!
## Grid and gap comparison for *same* stored maps and cutoffs
-/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace YM.OPE.Coverage
open Set Function Filter MeasureTheory Extraction Climb RG Table Ward Next.UVStress Spec Maxwell
open scoped Topology BigOperators ContDiff Classical
open Extra
open WeakScaling
variable {G:Gauge}{F:Order}{C:Family G}{S:Table C.book}{d D n n':ℕ}{μ R:ℝ}{r:ℕ→ℝ} (H:Final C F S)
set_option quotPrecheck false
local notation "s₀"=>H.sector.derivatives
local notation "T₀"=> Bel C.book
local notation "V" =>(T₀).Field
variable (p:Stored H r D n μ)
local notation "A" => p.maps
local notation "ρ"=> p.path
local notation "B"=> fun i=>(p.wheel i).spacing

variable (hr:0<R)(hμ:R≤μ)
include hr hμ
lemma finer_tags {t:Caps n'}{u:record C t} (hn:n'≤n) (hv:∀ j,t j ≤ D): Sampled (apart R n') B (readMap A ρ (hang t (depthWord t u))) (Ward.disc (hang t (depthWord t u))) := by
   intro σ hσ x hx z he hG
   let w:=depthWord t u; obtain ⟨e,a,c,hh⟩:=p.receipt.proof_ n' hn t hv u
   let g j:= Extraction.tag (B (σ j)) (z j)
   let h(k:ℕ):=disc (hang t w) (g k)
   have hz:Tendsto h atTop (𝓝 (disc (hang t w) x)):= by
      have hs:=smoothDisc (Maxwell.table_smooth _) (hang t w)
      have hh:= apart_conf hr hx
      exact (hs.continuousOn _ hh).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨he, he.eventually ((conf_open _).mem_nhds hh)⟩)
   have hq:= (apart_in n' hr ((hμ.trans (?room:μ≤2*μ))))
   case room=> linarith
   have hall(x':Points n'): x'∈Scaling.window (2*μ) n' → x'∈conf n':= fun hx=> spaced_conf (by have hμ_1:=hr.trans_le hμ; positivity) hx.1
   have hi: ∀ᶠ k in atTop, ‖readMap A ρ (hang t w) (σ k) (g k)- h k‖ ≤ e (σ k):=by
      filter_upwards [hσ.eventually hh.costs, he.eventually ((apart_open _ _).mem_nhds hx), hG] with k hh hg hG
      let i:=σ k
      obtain ⟨l,hb,hF,hT⟩:=p.coup i
      choose y ht' hy using fun j=>hT ⟨t j,Nat.lt_succ_of_le (hv j)⟩ (w j)
      have hp:=p.spot i
      have hp': S.classTokens ∘ ripped (C:=C) y=routed A i ∘ hang t w:= funext (fun j=> Sigma.ext rfl (heq_of_eq (hy j).symm))
      have hEq:= (show readMap A ρ (hang t w) i (g k)=glow (p.wheel i) S y (g k) from ?eq)
      rw [hEq]; exact match_phase (p.wheel i) l hF w H.room.generic (tendsto_pi_nhds.mpr ht') hh _ (hq hg) hG
      case eq => unfold readMap disc;rw [← hp',← hp,S.at_project S H.room.kernel.laws.toSymmetric (fun _=>le_rfl) ((enlarged (p.wheel i|>.rad) _).1 (hall _ (hq hg)))]; exact Eq.refl _
   have hc : Tendsto (fun k=> readMap A ρ (hang t w) (σ k) (g k)- h k) atTop (𝓝 0):=tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) hi (hh.goes.comp hσ))
   simpa only [id_eq,zero_add, sub_add_cancel] using! (hc.add hz)

variable (hg:G.Simple)
include hg
omit hr hμ in
lemma finer_spacing (hn:0<n):Tendsto B atTop (𝓝 0):=by
  let t:Fin 1→ℕ:=fun _=>0; let u:=fun _:Fin 1 => (0:(T₀).Field 0)
  -- requires nonempty record C t; each finrank of Field0 at least one? Basis dimension might zero. Maxwell has unit !=0. prove.

  let d : record C t:=fun j=>⟨0, by rw [UVNext.FreeStress.dim_before C.labels hg (show t j<4 by decide)]; apply Nat.zero_lt_succ⟩
  have ht:∀i,t i ≤ D:= fun i=>Nat.zero_le _
  obtain ⟨a,b,c,hB⟩:=p.receipt.proof_ 1 hn t ht d
  have hh : ∀ᶠ i in atTop,0 ≤ B i ∧ B i ≤(p.wheel i).σ:= by
      filter_upwards [hB.room] with i hi
      norm_num at hi
      have h:0 ≤ B i:= (p.wheel i|>.space.le); refine ⟨h,?_⟩; linarith [show 4*(1:ℕ)*B i ≤ (p.wheel i).σ by simpa using hi]
  exact squeeze_zero' (hh.mono fun _ h=>h.1) (hh.mono fun _ h=>h.2) hB.stripe
private abbrev Zf {t:Caps n'} (x:(i:Fin n')→(T₀).Field (t i)):= hang t x
lemma finer_sample (v:Fin n'→ (T₀).Tag)(hn:n'≤n)(hv:capped D v):Sampled (apart R n') B (readMap A ρ v) (Ward.disc v):=by
 intro σ hσ X hx z₀ he hG
 let t(i:Fin n') := (v i).1; let x(i:Fin n'): V (t i) := (v i).2
 have hf(j:record C t):= finer_tags H p hr hμ (u:=j) (t:=t) hn hv σ hσ X hx z₀ he hG
 let dms := fun i:Fin n' => V (t i)
 let F(i:ℕ):= ((S.classMoment S t (ρ (σ i) • Extraction.tag (B (σ i)) (z₀ i))).compLinearMap fun j=> (A (σ i) (t j)))
 let F0:=(T₀).classMoment (T₀) t X
 have hg:= tendsto_finset_sum (Finset.univ:Finset (record C t)) (fun j _=> (hf j).const_mul (coords dms j x))
 have he :=basis_tuple _ x F0
 change F0 x = _ at he
 have hthy : Ward.disc v X=F0 x:=rfl
 rw [hthy,he]
 refine hg.congr fun i=>?_ -- rowwise
 exact (basis_tuple dms x (F i)|>.symm)
lemma finer_growth (hn:0<n) {t:Caps n'}{u:record C t} (hn':n'≤n)(ht:∀ i,t i ≤ D) : Follows (apart R n') (fun k x=> (B k) • readMap A ρ (hang t (depthWord t u)) k x) 0:=by
  intro σ hs x hx z hz
  obtain ⟨a,bb,c,hB⟩:=p.receipt.proof_ n' hn' t ht u
  obtain h|h:= (Nat.zero_le n').eq_or_lt
  · subst n'
    let w:= hang (n:=0) t (depthWord t u)
    have empty(k:Points 0): k ∈ conf 0:= fun i=>i.elim0
    let u : Fin 0 → C.book.Token:= fun i=>i.elim0
    have he(k): readMap A ρ w k = fun _:Points 0 => 1:=funext fun x=>by
      change S.useAt S _ _=_; rw [←(show S.classTokens ∘ u=routed A k ∘ w from funext (fun j=>j.elim0)), S.at_project S H.room.kernel.laws.toSymmetric (fun _=>le_rfl) (empty _)]; apply H.room.kernel.laws.trivial
    change Tendsto (fun i=> B (σ i) • readMap A ρ w ..) atTop _; rw [show (fun i=> (B (σ i)) • readMap A ρ w (σ i) (z i))=(fun i=>B (σ i) • (1:ℂ)) from funext (fun i=>(by rw [he]))]; change Tendsto _ atTop (𝓝 (0:ℂ)); rw [← zero_smul ℝ (1:ℂ)]; exact (((finer_spacing H p hg hn).comp hs).smul_const (1:ℂ))
  let g i:= ρ (σ i) • z i
  refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) (?bound : Filter.Eventually (fun i=> ‖_‖ ≤ _) atTop) (hB.off.comp hs))
  filter_upwards [hs.eventually hB.room,hs.eventually hB.costs, hz.eventually ((apart_open R n').mem_nhds hx)] with i hi hA hx
  let k:=σ i; let q:=p.wheel k; obtain ⟨l,k',hl,hk,hm,hCost⟩ := hA.crude
  have hh: ‖readMap A ρ _ _ _‖ ≤ _:= Window_spot H p t (depthWord t u) ht hCost (div_pos (q.rad) (by linarith)) hl hk hm (g i) (p.spot k ▸ centered_in (lt_of_lt_of_le hr hμ) (p.fades.1 k) _ (apart_in _ hr hμ hx))
  change 4*(↑n':ℝ)*q.spacing ≤ q.σ at hi
  have hm: (n':ℝ)≥1:= Nat.one_le_cast.mpr h
  have hf : q.spacing ≤ q.σ:= by exact (by calc q.spacing = 1*q.spacing := by ring
                                                _ ≤ (4*(n':ℝ))*q.spacing := mul_le_mul_of_nonneg_right (by linarith only [hm]) q.space.le : _ ≤ _).trans hi -- explicit
  calc ‖_‖ = q.spacing*‖readMap A ρ _ k (z i)‖ := by rw [norm_smul,Real.norm_of_nonneg q.space.le]
       _ ≤ q.spacing * (bb k)^n' := mul_le_mul_of_nonneg_left hh q.space.le
       _ = (bb k)^n' * q.spacing := mul_comm ..
       _ ≤ _:= mul_le_mul_of_nonneg_left hf ((norm_nonneg _).trans hh)

lemma grow_samples (v:Fin n' → (Bel C.book).Tag)(h:0<n)(hn:n'≤n)(hv:capped D v): Follows (apart R n') (fun j x=> (B j) • readMap A ρ v j x) 0:= by
   intro σ hσ X hx z₀ he
   let t(i:Fin n') := (v i).1; let x(i:Fin n'): V (t i) := (v i).2
   have hf(j:record C t):= finer_growth H p hr hμ hg h (u:=j) (t:=t) hn hv σ hσ X hx z₀ he
   let dms := fun i:Fin n' => V (t i)
   let F(i:ℕ):= ((S.classMoment S t (ρ (σ i) • z₀ i)).compLinearMap fun j=> (A (σ i) (t j)))
   have hg:= tendsto_finset_sum (Finset.univ:Finset (record C t)) (fun j _=> (hf j).const_mul (coords dms j x))
   have hh : ∀ i:Code dms,coords dms i x * (((0:Points _→ℂ) X):ℂ)=0:=fun i'=>mul_zero _
   simp_rw [hh,Finset.sum_const_zero] at hg
   refine hg.congr fun i=>?_
   have he :=basis_tuple _ x (B (σ i) • F i)
   exact he.symm
end YM.OPE.Coverage
