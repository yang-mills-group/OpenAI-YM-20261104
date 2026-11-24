import YM.X.Try.Trance
import YM.X.Scheme.Radar
/-!
# Compensated for arbitrary warm budget. A single playback frame radius chosen small enough. Useful for defining the triangulated signature
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tri
open Lattice Wilson Maxwell Maxwell.Free MvPolynomial Function Set Filter MeasureTheory
open PertExtension LatticePT Heat.Top Next.Rank Next.Rank.Normal
open Pert Pert.Position Pert.RawLabels Pulse Bare Ribbon
open Interval.Size Hinge Reed Stems Haze Gravity Crate Interval
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{q:ℕ+}{F:Labels.Frames G} {d n k m:ℕ} {V W I:Type*} {r R:ℝ}
local notation "A"=> Bank F d
-- footprints at any heights supported
section
variable (t:Test m)(hq:1<q.val)(f:(i:ℕ)→Native q i→Grid.offsets q m i→ℂ) {g:Points m→ℂ}{K:Set (Points m)}
include hq
lemma pay_integral (hK:IsCompact K) (h:∀ a:Beam q,(∀i,a i∈origins q i)→∀ x∈K,∀ v:(i:ℕ)→Grid.offsets q m i,clockP x v→ Tendsto (fun i=>f i (a i) (v i)) atTop (𝓝 (g x))) (hp:∀ x∉K,g x=0)(hw:∀i:ℕ,∀a:Native q i,∀v:Grid.offsets q m i, Grid.sample q i v∉K→ f i a v=0): Integrable g ∧ Tendsto (fun i=> payL q m i (f i)) atTop (𝓝 (∫ x, g x)) := by
    have he (L':ℂ→L[ℝ]ℝ) (a:Beam q)(ha:∀i,a i∈origins q i): Integrable (fun x=>L' (g x)) ∧ Tendsto (fun i=> epsilon q i^(4*m) * ∑ v:Grid.offsets q m i, L' (f i (a i) v)) atTop (𝓝 (∫ x,L' (g x))) := Grid.integrable_spots hq (K:=K) (F:=fun i v=>L' (f i (a i) v)) (fun s x hx hs=> L'.continuous.continuousAt.tendsto.comp (h a ha x hx s hs)) hK (fun i k ht=>by rw [hw _ _ _ ht,map_zero]) (T:=fun x=>L' (g x)) (fun i hi=>by rw [hp i hi,map_zero])
    choose a ha using fun i=> hasOrigin q i; let A':=Complex.reCLM; let B':= Complex.imCLM; have hg: Integrable g:= by
        let L:=Complex.ofRealCLM; let t:=Complex.I; have hX:= L.integrable_comp (he A' a ha).1; have hY:= L.integrable_comp (he B' a ha).1; exact (hX.add (hY.mul_const t)).congr (Eventually.of_forall fun i=> Complex.re_add_im ..) -- real comp name
    refine ⟨hg,?_⟩; have hy (L':ℂ→L[ℝ] ℝ) : Tendsto (fun i=> L' (payL q m i (f i))) atTop (𝓝 (L' (∫ x,g x))):= by
       rw [← L'.integral_comp_comm]; simp_rw [payL,map_smul,map_sum,map_smul,map_sum]; apply Grid.average_paths (f:=fun m' o=>epsilon q m'^(4*m)*∑ v:Grid.offsets q m m', L' (f m' o v)) (hn:=fun i=> hasOrigin q i);
       · intro a ha; exact (he L' a ha).2
       exact hg
    exact touchℂ (hy Complex.reCLM) (hy Complex.imCLM) -- edit
end
abbrev Workroom (F:Labels.Frames G) (d:ℕ):= Module.End ℂ (E F d)
def billM (F:Labels.Frames G) (P:Workroom F d)(v:Bank F d) : Bank F d:= fun m t=> passV P (v m t)
variable (S:Bare.Shop F) {p:Fin m→ Pert.Position.E F d} (t:Test m)(L:ℕ→ Workroom F d) (hq:1<q.val) (hg:G.Simple)
def remit (q:ℕ+) (F':Bare.Shop F)(L₀:ℕ→ Workroom F d) (i:ℕ): Bank F d:= F'.bank q i d 1-billM F (L₀ i) (F'.bank q i d 0)
def point (q:ℕ+) (S:Bare.Shop F) (b:Workroom F d)(i:ℕ)(x:Grid.offsets q m i) : alma (E F d) m:= outerK S (epsilon q i) x d 1 - passV b (outerK S (epsilon q i) x d 0)
def probeX (q:ℕ+) (S:Bare.Shop F) (b:Workroom F d)(i:ℕ)(x:Grid.offsets q m i) : alma (E F d) m:= partM S _ (epsilon q i) x d 1 - passV b (partM S _ (epsilon q i) x d 0)
lemma point_val (p:Fin m→ E F d): remit q S L k m t p=tallyM t q k (fun x=> point q S (L k) k x p):= by
   unfold remit; simp only [Pi.sub_apply,MultilinearMap.sub_apply]; unfold billM; simp_rw [point,MultilinearMap.sub_apply, pass_view, bank_time, ← tally_sum]; exact (tally_sub t _ (∑ i:Fin m,(fun x=>outerK S (epsilon q k) x d 0 (Function.update p i ((L k) (p i)))))).symm.trans (congr_arg _ (funext (fun x=> by rw [Pi.sub_apply,Finset.sum_apply]))) -- name clashes
variable (b:Pert.Position.Section F d)(HB:∀v:E F d,(fun i=> L i v)∈ Trust q (E F d)) (hL: balance q S r m L)
variable {x:Points m} (a:Beam q)(ha:∀i,a i∈ origins q i)(v:(i:ℕ)→ Grid.offsets q m i)(hv:clockP x v)
local notation "Gᵥ" k=>storefront q k (v k) (a k)
include hq hg hv ha HB
lemma cut_out (p:Fin m→ E F d): Tendsto (fun k=> point q S (L k) k (Gᵥ k) p-probeX q S (L k) k (Gᵥ k) p) atTop (𝓝 0):= by
    let y(j:Fin m)(i:ℕ):= lift (v i j); let t(j:Fin m):Beam q:=fun i=> Crate.Fund.postal y (a i) i j; have hp (j):Fielding.plot q (y j) (x j):= Grid.sample_each hq hv j; refine Tendsto.congr ?_ ((courtesy S L t a (at_origin a ha) (fun i=>on_neighbor a (y i) (hp i)) hq hg HB p).goes hq); intro k; unfold t Crate.Fund.postal Crate.Fund.stock y; simp_rw [wrap_lift];rfl
include hL
lemma out_run(xh:x∈Pulse.Region m r) (p:Fin m→ E F d) : Released (fun k=> point q S (L k) k (Gᵥ k) p):= by
    let y(j:Fin m)(i:ℕ):= lift (v i j); let t(j:Fin m):Beam q:=fun i=> Crate.Fund.postal y (a i) i j; have hp (j):Fielding.plot q (y j) (x j):= Grid.sample_each hq hv j; obtain ⟨C,h⟩:= hL y x.ofLp hp xh a p; have hp : Tendsto (fun i=> probeX q S (L i) i (Gᵥ i) p) atTop (𝓝 C) := by unfold Crate.Fund.postal Crate.Fund.stock y at h; simp_rw [wrap_lift] at h;exact h
    have hh:= (cut_out S L hq hg HB a ha v hv p).add hp; rw [zero_add] at hh; exact ⟨_,hh.congr (fun i=> sub_add_cancel .. )⟩
omit ha hv
lemma porch_value (p:Fin m→ E F d): ∃ g:Points m→ℂ,∀a:Beam q,(∀i,a i∈ origins q i)→∀ v:(i:ℕ)→Grid.offsets q m i,∀x∈Pulse.Region m r,clockP x v→ Tendsto (fun i=> point q S (L i) i (storefront q i (v i) (a i)) p) atTop (𝓝 (g x)):= by
     let g (i:ℕ)(a:Native q i)(v:Grid.offsets q m i):= point q S (L i) i (storefront q i v a) p; choose! c hc using fun x (hx:x∈Pulse.Region m r)=> single_gate g x hq (fun a ha v hv=> out_run S L hq hg HB hL a ha v hv hx p); exact ⟨c,fun a ha v x hx=>hc x hx a ha v⟩
def presence (v:Fin m→ E F d) := (porch_value S L hq hg HB hL v).choose
include ha hv in
lemma evident (p:Fin m→ E F d)(hx:x∈Pulse.Region m r): Tendsto (fun i=> point q S (L i) i (Gᵥ i) p) atTop (𝓝 (presence S L hq hg HB hL p x)):= (porch_value S L hq hg HB hL p).choose_spec a ha v x hx hv
set_option maxHeartbeats 450000 in
omit hg HB hL in
lemma score_trk (hv:clockP x v) : Tendsto (fun i=> score (epsilon q i) t (Grid.sample q i (v i))) atTop (𝓝 (t x)):= by
    let L:= fun i=> (epsilon q i, Grid.sample q i (v i)); have he : Tendsto L atTop (𝓝 ((0:ℝ),x)):= (Interval.paths hq).cutoff.prodMk_nhds (show Tendsto (fun i=>Grid.sample q i (v i)) atTop (𝓝 x) from hv)
    let f(w:ℝ× Points m):= score w.1 t w.2; have ht:= Continuous.tendsto (score_cont t) ((0:ℝ),x)
    change Tendsto f _ (𝓝 (score 0 t x)) at ht; rw [score_origin] at ht; change Tendsto (f ∘ L) _ _; exact ht.comp he
lemma inside (p:Fin m→ E F d)(h: Curve t⊆ Pulse.Region m r): let g:= presence S L hq hg HB hL p; Integrable ((t:Points m→ℂ)*g) ∧ Tendsto (fun k=> (remit q S L k) m t p) atTop (𝓝 (t.applyTo g)):= by
    intro g; let f(k:ℕ)(a:Native q k)(v:Grid.offsets q m k):= score (epsilon q k) t (Grid.sample q k v)*point q S (L k) k (storefront q k v a) p; simp_rw [point_val S t]; -- order L predictor
    apply pay_integral hq f (region_compact t) -- hfg
    · intro a ha x hx v hv; have ht:= score_trk t hq v (x:=x) hv; have hn:= ht.mul (evident S L hq hg HB hL a ha v hv p (h hx)); exact hn
    · intro x hx; rw [Pi.mul_apply, show t x=0 from image_eq_zero_of_notMem_tsupport (fun h=> hx (Subcell.includes (tsupport (⇑t)) h)),zero_mul]
    intro i a v hv; unfold f; rw [score_dead t hq hv,zero_mul]
end YM.PositionX.Tri
