import YM.RG17.Pitch
import YM.RG17.Storage

/-!
# Real leading at the pegs with all orthogonal symmetries

Exacts available on measured sparse contour.
Not yet log law (need either Point or integrated Radiative data and
translation payments).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec Extraction Table OPE OPE.Orbits
open Next.UVStress Trace SharpGram Climb Ward
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{f: Extraction.Order}{S:Table C.book}{F:Final C f S}
    {u : Filter (ℕ×ℕ)}{B:Lenses.Mantle F u}{L:Layout F}(E:Services C f S)
set_option quotPrecheck false
local notation "N!"=> Maxwell.freeTable C.labels
local notation "P!"=>portal L
local notation "θ"=> fun k=> Load.tent B k
local notation "R"=> B.radius
variable {n:ℕ}{d:Fin n→ℕ}
    (z : Labels (Maxwell.freeTable C.labels) d)
    {s: Extraction.Sequence}
abbrev offsetPath (B:Lenses.Mantle F u) (s:Extraction.Sequence) : ℕ→ ℝ := B.radius ∘ ⇑s
structure Stands (L:Layout F) (B:Lenses.Mantle F u) (s: Extraction.Sequence) : Prop where
    pegs : Pegs B L
    match_length : ∀ i:ℕ,L.level (offsetPath B s i)=s i
local notation "r!"=> offsetPath B s
private def fitted (k:ℕ) : Labels N! d := fun i=> (B.lens k (d i)).symm (θ k (d i) (z i))
private lemma lifted (k:ℕ) : panels (Lenses.testLens (B.lens k)) ∘ hang d (fitted (B:=B) z k)=
    Orbits.tags (d:=d) (fun i=>θ k (d i) (z i)):=by funext i; exact congr_arg (Sigma.mk (β:=S.Field) (d i)) ((B.lens k (d i)).apply_symm_apply (Load.tent B k (d i) (z i)))
lemma poised_here (h:Stands L B s)(d i) : L.frame d (r! i)=θ (s i) d:= by rw [h.pegs.frame,h.match_length]
include E
lemma flex (h:Stands L B s) (ψ:Test n) : Tendsto (fun i=> plate (d:=d) (fun j=> L.frame (d j) (r! i) (z j)) (r! i) ψ) atTop (𝓝 (plate z 1 ψ)):=by
    have hx:= B.every_test (p:=d) (fitted (B:=B) z) z (fun i=> Load.seats B E (d:=d i) tendsto_const_nhds); have hg:=(hx.at_test ψ).add_const (plate z 1 ψ); rw [zero_add] at hg
    apply (hg.comp s.cofinal).congr; intro k
    let v:= fitted (B:=B) z (s k)
    change ψ.applyTo (tested (B.radius (s k)) (Lenses.testLens (B.lens (s k))) (hang d v) - disc (hang d z))+_= plate (d:=d) (fun j=> L.frame (d j) (r! k) (z j)) (r! k) ψ
    rw [test_sub]; rotate_left
    · exact (smoothZoom F.room.kernel.smooth _ (B.positive _)|>.continuousOn)
    · exact (smoothDisc (Maxwell.table_smooth _) _).continuousOn
    have hp: plate z 1 ψ=ψ.applyTo (disc (hang d z)):=by apply ψ.apply_eq; intro x _; simp only [one_smul]; rfl
    rw [hp, sub_add_cancel]
    simp only [poised_here h]; apply ψ.apply_eq; intro x _; unfold Next.UVStress.tested; rw [show panels (Lenses.testLens (B.lens (s k))) ∘ hang d v = _ from lifted z (s k)]; rfl
lemma pegScalar (h:Stands L B s){x:Points n}(hp:x∈conf _): Tendsto (fun i=> S.useAt S (r! i • x) (tags (d:=d) (fun j=> L.frame (d j) (r! i) (z j)))) atTop (𝓝 (disc (hang d z) x)):=by
    rw [Metric.tendsto_nhds]; intro ε hε
    filter_upwards [s.cofinal.eventually (B.uniformJets (p:=d) (fitted (B:=B) z) z (fun i=> Load.seats B E (d:=d i) tendsto_const_nhds) 0 {x} isCompact_singleton (singleton_subset_iff.mpr hp) (ε/2) (half_pos hε))] with i hi
    have hx:= hi x rfl;rw [← iteratedFDeriv_sub_apply, norm_iteratedFDeriv_zero] at hx;rotate_left
    · exact (smoothZoom F.room.kernel.smooth _ (B.positive _) _ hp|>.contDiffAt ((conf_open _).mem_nhds hp)).of_le (by simp)
    · exact (smoothDisc (T:= N!) (Maxwell.table_smooth _) (hang d z) _ hp|>.contDiffAt ((conf_open _).mem_nhds hp)).of_le (by simp)
    rw [dist_eq_norm]; simp only [poised_here h]; refine le_trans ?_ hx |>.trans_lt (half_lt_self hε); simp only [Pi.sub_apply,Next.UVStress.tested,lifted]; exact le_rfl
lemma centerFee (h:Stands L B s):Tendsto (fun i=> first_value 4 (scalarRay P! (r! i))) atTop (𝓝 0):=by
    rw [← mean_scalar_free (C:=C)]; have hh:=pegScalar E (d:=fun _:Fin 1=>4) (z:=fun _=>φS C) h (x:=(0:Points 1)) (valid_one _)
    exact hh.congr (fun i=>by rw [smul_zero]; rfl)
lemma pieces (h:Stands L B s): Tendsto (fun i=> Kdiag P! (r! i)) atTop (𝓝 (↑(theoryDensity G):ℂ)):=by
   let x:=separated 1
   have hx:x∈conf _:=room_conf x 0 _ _ _ (room_separated _ zero_le_one) one_pos one_pos
   have hN : disc (scalarCompar (C:=C)) x= (↑(theoryDensity G):ℂ):= by
     rw [Trace.free_expression x hx]
     have ht : span2 x =1:=by change ‖(1:ℝ) • basis timeAxis - 0‖=_; rw [sub_zero,one_smul,basis_time_bound]
     rw [norm_sub_rev]; rw [show ‖x 1 - x 0‖=1 from ht]; norm_num
   have ht:= pegScalar E (d:=fun _:Fin 2=> 4) (fun _=>φS C) h hx; rw [show hang _ _=scalarCompar (C:=C) from rfl,hN] at ht
   have hv:=ht.sub ((centerFee E h).pow 2); rw [zero_pow (by decide : 2≠0),sub_zero] at hv; apply hv.congr (fun i=>?_)
   have hp : 0 < r! i:= B.positive _
   unfold Kdiag;rw [focus_read F.room.kernel _ (room_conf _ 0 _ _ _ (room_separated _ hp.le) hp one_pos)]
   have hy : r! i • x=separated (r! i) := by
       apply PiLp.ext; intro j; fin_cases j
       · change r! i • (0:E4)=0; rw [smul_zero]
       change r! i • ((1:ℝ) • basis timeAxis)=_; rw [one_smul]; try rfl
   rw [hy]; congr 1
   rw [custom_self]; rfl
end YM.RG17
