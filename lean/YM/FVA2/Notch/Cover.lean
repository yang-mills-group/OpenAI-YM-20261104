import YM.FVA2.Notch.Platter
import YM.FVA2.Removal.Rates
/-! # Allowed placement setups: distance from D or at any mark.

 Placement for `Quiz`, `Card`: when working with `Sample`, can use **any** common center placement meeting the
 margin under study, not only the strip $[P/8,P/4]^4$. In fact clearance of floor(center)
 is NOT required if there is at least one insertion: can use instead the required clearance
 at a **single** arbitrary mark. On point profiles, all other marks are in the same bounded
 physical diameter so the period comparison can use $a^{-C}$ moments. Quantifier *uniform*
 simultaneously over all these setups. If there is no mark at all, even no clearance necessary.

 As before, do not assert anything on protocols taking nonseparated placements as part of
 profile (none used; require appropriate predicates on Samples). -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Notch
open Function Filter Set Finset Metric MeasureTheory Real Lattice MS MS.High
open MS.Book MS.Book.Convolve MS.Tone MS.Tide MS.Rake MS.Land MS.Dial MS.Orbit MS.City MS.Latch MS.Latch.Job MS.Fleet MS.Vista
open Wilson Further XSpace.Cirrus Arrival Arrival.Landing Arrival.Schedule Removal
open scoped Topology ContDiff BigOperators Classical
variable {n:ℕ} {K:Set (Points n)}{μ r:ℝ}
local notation "U"=> Fin n
local notation "Z"=> XSpace.Cirrus.Sample n
local notation "Zf"=> XSpace.Cirrus.grab (n:=n)
variable (p:XSpace.Cirrus.Sample n)

def Apart (r:ℝ)(A:Cover): Prop:= ∀ b:Half,wide r (wrap ( periodN ( psi p.F ) ) A - thin ( psi p.F ) b)
def Entry (r:ℝ)(p:XSpace.Cirrus.Sample n): Prop:= Apart p r (bar p) ∨ (∃ i, Apart p r (p.layout i)) ∨ n=0
private def along (A:Cover): Prop:= A=bar p ∨ (∃ i,A=p.layout i) ∨ n=0
lemma Apart.le {A:Cover}(h: Apart p r A)(b:ℝ)(hb:b≤r): Apart p b A:= fun i=> (mul_le_mul_of_nonneg_right hb (by positivity)).trans (h i)
omit p
-- I index for unconditional use (not eventually excluding vacuous compacts).
def Flight (r:ℝ)(K:Set (Points n)):= {p:Sample n // Entry r p ∧ familiar p ∈ K ∧ p.F.spacing ≤ 1∧ 16≤ p.F.p.side.val }
namespace Flight
variable (i:Flight r K)
local notation "p'"=> XSpace.Cirrus.Sample n
abbrev sample : Sample n := i.1

lemma signs : Entry r i.sample ∧ familiar i.sample ∈ K ∧ (i.sample).F.spacing≤1 ∧ 16≤(i.sample).F.p.side.val:= i.2
private lemma permit : ∃ A,Apart i.sample (min r (1/16)) A ∧ along i.sample A:= by
 rcases (signs i).1 with h|⟨k,hk⟩|h; exact ⟨ _, h.le _ _ (min_le_left ..),Or.inl rfl⟩; exact ⟨_, hk.le _ _ (min_le_left ..),Or.inr (Or.inl ⟨_,rfl⟩)⟩; -- pattern hk identifies index b
 let j: Sample n:= ⟨(i.sample).F,i.sample.layout,river (i.sample).F⟩; have H:Sized j:=⟨ (signs i).2.2.2, (signs i).2.2.1,sits (i.sample).F ⟩; refine ⟨ bar j,fun x=>?_,Or.inr (Or.inr h)⟩; change wide (min r (1/16)) ( wrap _ (bar j) - thin (psi j.F) x ); apply (mul_le_mul_of_nonneg_right ( min_le_right r (1/16:ℝ) ) (by positivity : 0≤ ((periodN (psi j.F)).val:ℝ)) ).trans; linarith [MS.Vista.E_n _ ( Schedule.cleared j H x )]
/-- actual unwrapped anchor, can be arbitrary periods away from origin -/
def peg (i:Flight r K) : Cover:= (permit i).choose
-- setup fixes origin only after picking peg.
def trail (r:ℝ)(K:Set (Points n))(μ:ℝ) : Trial (Flight r K) (Fin n) where
 profile:= ⟨ fun i=> theta i.sample.F,fun i=> μ-theta i.sample.F,fun _=> le_max_right .. ⟩
 side i:=psi i.sample.F
 off a i:= i.sample.layout a-i.peg
 head i:= Lattice.lift ( wrap ( periodN ( psi i.sample.F ) ) i.peg )
local notation "Q"=> trail r K μ
lemma adequate (hr:0<r) : Adequate (trail r K μ).side (trail r K μ).head:= ⟨ min r (1/16),lt_min hr (by norm_num),fun i x=> by change wide ( min r (1/16) ) (wrap ( periodN ( psi i.sample.F ) ) (Lattice.lift ( wrap ( periodN ( psi i.sample.F ) ) i.peg ))-thin ( psi i.sample.F ) x); rw [wrap_lift]; exact (permit i).choose_spec.1 x ⟩
-- physical offset between arbitrary positions is independent of chosen anchor, agrees with test profile
lemma symbol (i:Flight r K)(μ:ℝ)(w u:Fin n): testP (trail r K μ) i w-testP (trail r K μ) i u= plot ( familiar i.sample ) w- plot ( familiar i.sample ) u:= by
 let q:=i.sample; let p:= showR (n:=n) μ; have hx: q.F.spacing≤1:= (signs i).2.2.1; calc
   _ = exp (-theta q.F) • embed ( q.layout w - q.layout u ):= by change _• embed _- _•embed _= _; rw [← smul_sub,← emb_sub]; congr 2; change q.layout w- i.peg-( q.layout u-i.peg )=_; abel
   _ = testP p q w-testP p q u:= by rw [show q.layout w-q.layout u = σ q w-σ q u from (by unfold σ; abel), emb_sub, smul_sub ]; rfl
   _ = _:= by rw [show p=showR (n:=n) μ from rfl,planes _ μ _ hx,planes _ μ _ hx, add_sub_add_right_eq_sub] -- lemma name check
omit i
lemma in_box (hK:IsCompact K)(w u:Fin n): ∃ C:ℝ,0<C∧ ∀ x∈ K, ‖plot x w-plot x u‖≤ C := by
 obtain ⟨c,h⟩:= ( hK.image ( Continuous.norm ((( continuous_apply w ).comp plot_exposes).sub (( continuous_apply u ).comp plot_exposes )) ) ).bddAbove; exact ⟨ max 1 c,lt_of_lt_of_le zero_lt_one (le_max_left ..), fun x hx=> le_trans ( h ( Set.mem_image_of_mem _ hx ) ) (le_max_right 1 c) ⟩
lemma shifted (hK:IsCompact K) {w u:Fin n} (H:K⊆ conf n)(hu:w≠u) : ∃ c:ℝ,0<c∧ ∀ x∈ K, c ≤ ‖plot x w-plot x u‖:= by
 rcases K.eq_empty_or_nonempty with he|he; · exact ⟨1,zero_lt_one, he ▸ by simp⟩
 let f(x:Points n):ℝ:= ‖plot x w-plot x u‖; obtain ⟨p,hp,hQ⟩:= hK.exists_isMinOn he ( show Continuous f from Continuous.norm ((( continuous_apply w ).comp plot_exposes).sub (( continuous_apply u ).comp plot_exposes )) ).continuousOn; exact ⟨ f p,norm_pos_iff.mpr ( sub_ne_zero.mpr ( (track (H hp)).ne hu ) ),fun x hx=> hQ hx⟩
variable (hK:IsCompact K)(hr:0<r)(hO:K⊆ conf n)
include hK
open MS.Vane
lemma enough (μ:ℝ)(w:Fin n): ∃ C:ℝ,0<C∧ ∀ i:Flight r K,‖testP (trail r K μ) i w‖≤ C:= by
 obtain ⟨c,hc⟩:= ( hK.image ( Continuous.norm (( continuous_apply w ).comp plot_exposes) ) ).bddAbove; choose B hB b using in_box hK w; let m:= ∑ u:Fin n,B u; have hm:0≤ m:= Finset.sum_nonneg fun i _=>(hB i).le; refine ⟨ max 1 (1+c)+m,by linarith [le_max_left (1:ℝ) (1+c)],fun i=>?_⟩
 let p:=i.sample; rcases (permit i).choose_spec.2 with H|⟨u,hu⟩|Hu
 · have h (w:Fin n) : testP (trail r K μ) i w=testP ( showR μ ) p w:=by
      change exp _•embed (p.layout w-i.peg)= exp _ • embed _; rw [show i.peg=bar p from H]; rfl
   rw [h]; let x:= plot ( familiar p ) w; let y:= testP (showR μ) p w; have hl: ‖y-x‖≤ 1:= ( approaches p μ w ( signs i ).2.2.1 ).trans (signs i).2.2.1; have he: ‖x‖≤c:= hc (Set.mem_image_of_mem _ (signs i).2.1)
   change ‖y‖≤_; exact le_trans ( ( show ‖y‖≤ ‖y-x‖+‖x‖ from by simpa only [sub_add_cancel] using norm_add_le (y-x) x ) ) ( by linarith [le_max_right (1:ℝ) (1+c)] )
 · have he := symbol i μ w u; have hU:testP (trail r K μ) i u=0:= by change _•embed (p.layout u-i.peg)=_; rw [show peg i=p.layout u from hu,sub_self,show embed 0=0 from (by ext; simp [embed]),smul_zero]; -- name check
   rw [ hU,sub_zero ] at he; rw [he]; have hZ:B u ≤ m:= Finset.single_le_sum (f:=B) (fun i _=> (hB i).le) (Finset.mem_univ u); exact le_trans ( b u _ (signs i).2.1 ) ( by linarith [le_max_left (1:ℝ) (1+c)] )
 · have h':=w.isLt; omega
include hr hO
lemma worthy (μ:ℝ): Spots (trail r K μ) μ:= by
 let p:= trail r K μ; refine ⟨fun i=>?_,fun _=>rfl, unpose ( v:=μ ) p.off ?_,adequate hr, centered_size _ _ fun i=>?_⟩
 · obtain ⟨c,hc,h⟩:= enough ( r:=r ) hK μ i; refine ⟨ c,hc,fun j=>?_⟩; let a:= exp ( p.profile.θ j ); have hh:=h j; change ‖exp (-p.profile.θ j)•embed (p.off i j)‖ ≤ c at hh; rw [exp_neg,norm_smul_of_nonneg ( by positivity ) ] at hh; change ‖embed ( p.off i j )‖≤ _*a; rw [mul_comm]; exact (inv_mul_le_iff₀ (by unfold a; positivity)).1 hh
 · intro i j hij; obtain ⟨c,hc,h⟩:= in_box hK i j; obtain ⟨D,hD,H⟩:= shifted hK hO hij; refine ⟨ ⟨ c,hc,fun x=>?_⟩,⟨ D,hD,fun x=>?_⟩ ⟩ <;> rw [show MS.Rake.Geo.roots ( frameF _ μ ) _=1 from exp_zero,mul_one]; · change ‖testP p x i-testP p x j‖ ≤ c; rw [show p=trail r K μ from rfl,symbol]; exact h _ (signs x|>.2.1)
   change _ ≤ ‖testP p x i-testP p x j‖; rw [show p=trail r K μ from rfl,symbol]; exact H _ (signs x|>.2.1)
 change Lattice.lift ((wrap (periodN (psi i.sample.F))) i.peg)= Lattice.lift (wrap ( periodN (psi i.sample.F) ) (Lattice.lift ( wrap ( periodN (psi i.sample.F) ) i.peg ))); rw [wrap_lift]; -- rfl?
end Flight
end YM.FVA2.Notch
