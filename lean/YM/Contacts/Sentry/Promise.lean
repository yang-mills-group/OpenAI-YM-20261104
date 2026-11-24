import YM.Contacts.Sentry.Single
import YM.Contacts.Power.Level
import YM.Contacts.Power.Shorter
import YM.MergeProof.West.Compass
/-!
# Cover/exterior rates

Output with specifically charged Slot against nested exterior shape. Positional
jets along translated choices may use the same field filtration in the same
hierarchy. Provide rates `Sharp ε`; no requirement relative spacings are
comparable to each other. Vital when one distinguished field is the output of
another comparison. Using crude counting and old phase slabs alone would charge
its weight at the wrong radius.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Sensor
open Function Set Filter MeasureTheory Extraction Lattice Cells Word Wilson Costar Bid Next.Phase
open Extraction.Gaps Extraction.Spin Analysis Table Org Spec MergeProof.Ribbons Power Ward Next.UVStress
open scoped Topology BigOperators ContDiff
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(V:Final C F S)
variable {ι:Type*}
-- adapt centered exponential budgets from Compass (2→ any slack at station). note not polylog.
include V
lemma bench (w:C.book.Token){ε:ℝ}(he:0<ε): ∀ᶠ m in atTop, F.late (centeredBudget C w (Real.exp (((w.1:ℝ)+ε)*C.S.scale m)) m):=by
    obtain ⟨d,v⟩:=w
    obtain ⟨m₀,hp,A,hA,η⟩:= V.room.copies.centered d (ε/2) (‖v‖+1) (by linarith) (by positivity)
    let e:ℝ:= -(d:ℝ)-ε/2; let w i:= C.S.a i^e; have he:e ≤ 0:=by unfold e; linarith[Nat.cast_nonneg (α:=ℝ) d]
    have hh:Note C.S (fun i=>(A+1)*w i) (0+e*(-1)) := (Note.notes C.S _ (by linarith :0<A+1)).mills ((Note.note_a C.S).powr e)
    filter_upwards [eventually_ge_atTop m₀,hh.outweigh (Note.bell_exp C.S ((d:ℝ)+ε)) (by unfold e; linarith),C.S.shrinks.eventually (ge_mem_nhds (α:=ℝ) (by norm_num : (0:ℝ)<1))] with m hm hh hx
    apply (η _ hm 1 (by norm_num)).mono; intro i hi; refine hi.mono fun j hj=> ?_
    obtain ⟨h,hj⟩:= hj; refine ⟨h,hp.trans (hm.trans h),fun o => ⟨(hj v (by simp) o).1,(hj v (by simp) o).2.trans (?_)⟩ ⟩
    refine le_trans ?_ hh; rw [add_mul,one_mul]; exact add_le_add_right (Real.one_le_rpow_of_pos_of_le_one_of_nonpos (C.S.a_pos _) hx he) _

lemma spectral (x : C.book.Token) {ε:ℝ}(he:0<ε): ∀ᶠ m in atTop,F.late (Single C x (Real.exp (((x.1:ℝ)+ε)*C.S.scale m)) m):= by
    let T := fun i : Extraction.Spin.Frame => Extraction.Spin.token C.book x i
    filter_upwards [eventually_all.mpr fun i => bench V (T i) he] with k hk
    have ht : ∀ᶠ u:ℕ×ℕ in F.fuse, ∀ i,centeredBudget C (T i) (Real.exp ((((T i).1:ℝ)+ε)*C.S.scale k)) k u.1 u.2:= eventually_all.mpr fun i=> hk i
    have he : ∀ᶠ u in F.fuse, ∀ i, Around.Fit (T i) k u.1 u.2 := eventually_all.mpr fun i => by
        rw [Extraction.Order.fused]; exact Eventually.of_forall fun r => (Around.fit (f:=F) (T i) k).mono fun p hp => hp _
    change ∀ᶠ u in F.fuse,Single C x (Real.exp (((x.1:ℝ)+ε)*C.S.scale k)) k u.1 u.2; filter_upwards [ht,he, Next.UVStress.large_mesh F k] with u h hp hv
    refine ⟨hv,fun _ j=>⟨?_,hp j⟩⟩
    have hh:(T j).1=x.1 := by dsimp [T,Extraction.Spin.token]; split <;> rfl
    specialize h j; rw [hh] at h; exact h
include V -- bench may need include!
-- Produce ℓ^C weight rates with slack, fixed `log units`. Useful many times in exterior fills.
def drawer (C: Family G) (d:ℕ)(ε:ℝ)(m:ℕ):= Real.exp (((d:ℝ)+ε)*C.S.scale m)
variable {P:Pace ι}{b k l t:ι→ℕ}{μ ℓ α α' ρ ρ':ℝ}
variable (hb:Mesh P C.S b α)(hk:Mesh P C.S k α')(hl:Mesh P C.S l ρ)(ht:Mesh P C.S t ρ')

include hk in
lemma charged (x:C.book.Token) {ε:ℝ}(he:0<ε): P.Rating (((x.1:ℝ)+ε)*α') (drawer C x.1 ε ∘ k) ∧ ∀ᶠ i in P.net, F.late (Single C x (drawer C x.1 ε (k i)) (k i)):=
    ⟨hk.noted (Note.bell_exp C.S ((x.1:ℝ)+ε)), hk.cover.eventually (spectral V x he)⟩
include hb hk
omit V in
lemma space_budget (c:ℝ)(h:α<α'): ∀ᶠ i in P.net,c*C.S.a (k i) < C.S.a (b i):= hk.mesh_a -- adjust
   |>.priced |> fun hh=> hb.mesh_a.longer.strict ((Pace.Priced.constants c).mul hh) (by linarith only [h])

variable (g:Grill C F)(Y:ι→ Viewer V)
variable {j:Type}[Fintype j][DecidableEq j](w:j→ C.book.Token)(u:j)(x:ι→j→ E4)
structure Lit (u:j)(P:Pace ι)(x:ι→j→ E4)(μ ℓ:ℝ): Prop where
     side : ∀ i,i≠u→ P.Longer (-μ) fun s=> ‖x s i-x s u‖
     cost : ∀ i k,i≠k→ P.Longer (-ℓ) fun s=> ‖x s i-x s k‖
omit hb hk V
lemma Lit.hurry (hx:Lit u P x μ ℓ) : ∀ᶠ i in P.net, Injective (x i):= by
   filter_upwards [eventually_all.mpr fun i=> eventually_all.mpr fun k=> eventually_all.mpr fun h=> (hx.cost i k h).pos] with i hi j k hh; by_contra he; have h:=hi j k he; rw [hh,sub_self,norm_zero] at h; exact lt_irrefl _ h
include hb hl in
lemma lit_levels (hx:Lit u P x μ ℓ)(hμ:μ<α)(hℓ:ℓ<ρ): ∀ᶠ i in P.net, Blanket u (x i) (2*C.S.a (b i)) (2*C.S.a (l i)):= by
    let U:= (Pace.Priced.constants (P:=P) (2:ℝ))
    filter_upwards [eventually_all.mpr fun i=> eventually_all.mpr fun H=>(hx.side i H).strict (U.mul hb.mesh_a.priced) (by linarith), eventually_all.mpr fun i=> eventually_all.mpr fun j=> eventually_all.mpr fun H=> (hx.cost i j H).strict (U.mul hl.mesh_a.priced) (by linarith)] with i hi he
    exact ⟨hi,he⟩
include hb hk hl ht V g in
lemma mesh_price (hf:α<α')(hh:α'<ρ)(he:ρ<ρ')(hx:∀ᶠ i in P.net, Blanket u (x i) (2*C.S.a (b i)) (2*C.S.a (l i))) {ε:ℝ}(hε:0<ε) :
    P.Priced (∑ i, (((w i).1:ℝ)+ε)* if i=u then α' else ρ') fun i=> sample (watches V (Y i)) (x i) w:= by
   let E (a:j)(i:ι):= drawer C (w a).1 ε ((if a=u then k else t) i)
   have hB (i) : P.Rating ((((w i).1:ℝ)+ε)* if i=u then α' else ρ') (E i):= by unfold E; split_ifs; exacts [(charged V hk (w i) hε).1,(charged V ht (w i) hε).1]
   apply (Pace.Rating.prod Finset.univ E _ (fun i _=>hB i)).priced.capped_by
   filter_upwards [hb.thick hk hf, hk.thick hl hh, hl.thick ht he,hx,space_budget hb hk 8 hf,space_budget hl ht (6*(extras u).card) he, (charged V hk (w u) hε).2,eventually_all.mpr fun i=> (charged V ht (w i) hε).2] with i hb hk ht hx hp hZ hB hw -- x := hx invalid
   exact budget V g (Y i) u w (x i) (fun a=> E a i) hb.le hk.le ht.le hp hZ (fun _=> (Real.exp_pos _).le) (by simpa only [E,if_true] using hB) (fun a he=>by simpa only [E,if_neg he] using hw a) hx
include V g
lemma wages (hx:Lit u P x μ ℓ) (hμ:0≤μ)(hℓ:μ≤ℓ):
    P.Priced (∑ i, ((w i).1:ℝ)* if i=u then μ else ℓ) fun i=> sample (watches V (Y i)) (x i) w:= by
   let f e:= (∑ i, (((w i).1:ℝ)+e)* if i=u then μ+2*e else ℓ+4*e)
   have he (e:ℝ)(h:0<e): P.Priced (f e) fun i=> sample (watches V (Y i)) (x i) w:= by
       let G:= C.path.levels.fits.mesh
       obtain ⟨b,hb⟩:=Mesh.selectMesh C.S G P (show 0<μ+e by linarith)
       obtain ⟨k,hk⟩:=Mesh.selectMesh C.S G P (show 0<μ+2*e by linarith); obtain ⟨l,hl⟩:=Mesh.selectMesh C.S G P (show 0<ℓ+3*e by linarith); obtain ⟨t,ht⟩:=Mesh.selectMesh C.S G P (show 0<ℓ+4*e by linarith)
       exact mesh_price V hb hk hl ht g Y w u x (by linarith) (by linarith) (by linarith) (lit_levels hb hl u x hx (by linarith) (by linarith)) h
   have h : Continuous f:=by unfold f; refine continuous_finsetSum _ fun i h=> ?_; split_ifs; all_goals fun_prop
   simpa only [f,mul_zero,add_zero] using! (Pace.Priced.latitude0 ((show ∀ᶠ x:ℝ in 𝓝[>] 0,0<x from self_mem_nhdsWithin).mono he) h.continuousAt)

-- consumer uses physical
lemma values (d:j→ℕ)(w:∀ a:j,S.Field (d a))(hx:Lit u P x μ ℓ)(hμ:0≤μ)(hℓ:μ≤ℓ) :
    P.Priced (∑ i, (d i:ℝ)* if i=u then μ else ℓ) fun i=> corr (watches V (Y i)) (x i) (fun j=>(⟨d j,w j⟩:S.Tag)):=wages V g Y (expose ∘ (fun j=>(⟨d j,w j⟩:S.Tag))) u x hx hμ hℓ -- _ stuck?
end YM.Contacts.Sensor
