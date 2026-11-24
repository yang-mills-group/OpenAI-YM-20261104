import YM.PhysMS.Frame.Sections
import YM.Extra.WEAK_SCALING_ACTLAW.Adjust

/-! # Choose a graded meter coherently with the coupling diagnostic

Here "graded" means adapted to the filtration, not that there is no
field mixing. Also arrange *actual O(4)*, not just signed-axis symmetry,
using the homogeneous Maxwell grade section. (Later fit additional
subleading conditions on this type of meter.) Reuse the quantitative/near
identity mechanism of Extra.WeakScaling, adapt it to the *cap four
position prescription*, prove it doesn't disturb that prescription. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysMS.Frame
open Function Filter Set Table Spec Climb Spin Trace Trace.Pilot Extra.WeakScaling Next.UVStress
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}{C : Family G}{f : Extraction.Order}{S : Table C.book}
variable (F : Final C f S)(h:G.Simple)(H:(Bel C.book).Hierarchy)
local notation "M" => Bel C.book
local notation "R" => F.sector.turns
local notation "V" => F.sector.derivatives
local notation "K" => Maxwell.Free.scheme C.labels
set_option quotPrecheck false
local notation "D" d => (Bel C.book).Field d
local notation "L" s =>  V.rise (Nat.le_succ s)

section compatible
variable {p:Type*} {l:Filter p} {A X:p→tower S}
def Adjacent (P: p→tower S) (l:Filter p) := ∀ (d : ℕ) (v:(Bel C.book).Field d),
     Tendsto (fun i=> (P i (d+1)).symm ((V).rise (Nat.le_succ d) (P i d v))) l (𝓝 ((K).rise (Nat.le_succ d) v))
private lemma pullsTo {E:Type*} [NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
    {U:p → Mat E} (hU:Tendsto U l (𝓝 1)) {r:p→E} {x:E} (h:Tendsto (fun i=> U i (r i)) l (𝓝 x)) : Tendsto r l (𝓝 x):=by
    have he : Tendsto (fun k=> Ring.inverse (U k)) l (𝓝 1):=by
       rw [← Ring.inverse_one (Mat E)]; exact (NormedRing.inverse_continuousAt (1:(Mat E)ˣ)).tendsto.comp hU
    apply (Dash.arcing he h).congr'; filter_upwards [hU.eventually (Units.nhds (1:(Mat E)ˣ))] with k hk
    change (Ring.inverse (U k)*U k) (r k)=_;rw [Ring.inverse_mul_cancel _ hk]; rfl
lemma neighboring (hX:Adjacent F X l) (he:∀ d (v : (Bel C.book).Field d),
      Tendsto (fun i=> (X i d).symm (A i d v)) l (𝓝 v)) : Adjacent F A l:= by
  intro d v
  let U(i:p):= moveV (S:=S) (d+1) (X i (d+1)) (A i (d+1)); have hU:Tendsto U l (𝓝 1):=
     Dash.fit_plane (fun i=> actMove (S:=S) (d+1) (X i (d+1)) (A i (d+1)) |>.toLinearMap) LinearMap.id (he (d+1))
  let f i:= ((X i (d+1)).symm.toLinearMap.comp ((V).rise (Nat.le_succ d))).comp (X i d).toLinearMap; let r:= fun i=> (A i (d+1)).symm ((V).rise (Nat.le_succ d) (A i d v)); let P:= (K).rise (Nat.le_succ d)
  have hA:Tendsto (fun i=> U i (r i)) l (𝓝 (P v)):=by
      refine (Dash.arcing (Dash.fit_plane f P (hX d)) (he d v)).congr (fun i=>?_)
      change (X i (d+1)).symm ((V).rise _ (X i d ((X i d).symm (A i d v))))=(X i (d+1)).symm (A i (d+1) ((A i (d+1)).symm _)); rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  exact pullsTo hU hA

-- Use the same elementary recursion as in WeakScaling's finite-horizon proof.
private abbrev adjust (X:tower S) := adjusted F.sector.derivatives (Maxwell.Free.scheme C.labels) (peelDown C) X
def compatible (X:tower S) : tower S := fun d=> if h:Bijective (adjust F X d) then LinearEquiv.ofBijective _ h else X d
lemma compatible_at {X:tower S} (d : ℕ) (h:Bijective (adjusted F.sector.derivatives
    (Maxwell.Free.scheme C.labels) (peelDown C) X d)) (v : D d) : compatible F X d v=adjust F X d v := by
  rw [compatible,dif_pos (show Bijective (adjust F X d) from h)]; rfl
private abbrev adjustV (F:Final C f S)(A:p→tower S)(i:p)(d:ℕ) := (A i d).symm.toLinearMap.comp (adjust F (A i) d)

private lemma relative_limit (h:Adjacent F A l) (d : ℕ)(v:D d): Tendsto (fun i=> adjustV F A i d v) l (𝓝 v) := by
  induction d with
  | zero => exact tendsto_const_nhds.congr (fun i=> ((A i 0).symm_apply_apply _).symm)
  | succ d IH =>
    let K0:= K; let P:= K0.rise (Nat.le_succ d)
    let L0(i:p) := (A i (d+1)).symm.toLinearMap.comp (((V).rise (Nat.le_succ d)).comp (A i d).toLinearMap)
    let u:= peelDown C d v
    have hx:= Dash.arcing (Dash.fit_plane L0 P (h d)) (IH u); change Tendsto (fun i=> L0 i _) l (𝓝 (P u)) at hx
    have hp:= hx.add_const (v-P u); rw [add_sub_cancel ..] at hp; apply hp.congr; intro i
    change _= (A i (d+1)).symm (adjusted _ _ _ _ (d+1) v); rw [adjusted_succ,map_add,LinearEquiv.symm_apply_apply]
    change (A i _).symm ((V).rise _ (A i d ((A i d).symm _))) + _ = _; rw[LinearEquiv.apply_symm_apply]

private lemma bij (h:Adjacent F A l)(d : ℕ) : ∀ᶠ i in l, Bijective (adjust F (A i) d) := by
  have h₁:= Dash.fit_plane (fun i=> adjustV F A i d) LinearMap.id (relative_limit F h d)
  filter_upwards [h₁.eventually (ContinuousLinearMap.isOpen_injective.mem_nhds (show _ from injective_id))] with k hk
  have he : Injective (adjust F (A k) d) := Injective.of_comp (f:=(A k d).symm) hk
  exact ⟨he,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ((A k d).finrank_eq)).1 he⟩

lemma fitted_up (h:Adjacent F A l)(d:ℕ)(v:D d): Tendsto (fun i => (A i d).symm (compatible F (A i) d v)) l (𝓝 v):= by
  apply (relative_limit F h d v).congr'; filter_upwards [bij F h d] with k hk; rw [compatible_at F d hk]; rfl

private lemma adjacent_eq (X:tower S)(d : ℕ)(v : D d) : adjust F X (d+1) ((K).rise (Nat.le_succ d) v)= (V).rise (Nat.le_succ d) (adjust F X d v) := by
   unfold adjust; rw [adjusted_succ,section_up, sub_self,map_zero,add_zero]
private lemma brings (X:tower S)(d e : ℕ) (he:d ≤ e) (v:D d) : adjust F X e ((K).rise he v)= (V).rise he (adjust F X d v) := by
   induction e, he using Nat.le_induction with
   | base => rw [(K).arrival (Maxwell.table_sym _) (Maxwell.Free.scheme_filters _),(V).arrival F.room.kernel.laws.toSymmetric F.phase.transport.injection]
   | succ e h' ih=> rw [← (K).transit (Maxwell.table_sym _) (Maxwell.Free.scheme_filters _) h' (Nat.le_succ e),adjacent_eq,ih,(V).transit F.room.kernel.laws.toSymmetric F.phase.transport.injection]
lemma accounted (d e : ℕ) (he:d ≤ e) (h:Adjacent F A l) : ∀ᶠ i in l, ∀ v:D d,
    compatible F (A i) e ((K).rise he v)=(V).rise he (compatible F (A i) d v) := by
   filter_upwards [bij F h d, bij F h e] with i hf ht v
   rw [compatible_at F d hf,compatible_at F e ht]; exact brings F (A i) d e he v
abbrev obedient (B:tower S)(d : ℕ): Prop:= AlignO F.sector F.room.kernel.spin H d (B d)
include h
lemma obedient_realH {B:tower S}{d : ℕ}(he:obedient F H B d) : realH F.room.kernel.spin H.spin (B d) := by
    refine ⟨fun s v=> ?_, he.real⟩; rw [← (baseRights (H:=H) h).signed, he.axis, F.phase.transport.spots.signed]
private lemma plan_actual {A: tower S}(d : ℕ) (hA : ∀ k ≤ d, obedient F H A k) :
    (∀ x : (Bel C.book).Field d, S.conj F.room.kernel.spin d (adjust F A d x) = adjust F A d ((Bel C.book).conj H.spin _ x)) ∧
    (∀ s x, F.sector.turns.act d s (adjust F A d x) = adjust F A d ((turns C).act d s x)) ∧ adjust F A d ((Bel C.book).unit d)= S.unit d := by
  induction d with
  | zero => exact ⟨fun x=> ((hA 0 le_rfl).real _).symm, fun s x=> ((hA 0 le_rfl).axis _ _).symm, (hA 0 le_rfl).unit⟩
  | succ d ih =>
     obtain ⟨hP,hQ,hU⟩ := ih (fun k hk=> hA k (hk.trans (Nat.le_succ _)))
     have h₀ := hA (d+1) le_rfl
     refine ⟨fun x=> ?_, fun s x=> ?_, ?_⟩
     · unfold adjust at *
       rw [adjusted_succ, adjusted_succ, section_real H,map_add, F.phase.transport.rights.realInc,hP,← h₀.real, map_sub ((M).conj H.spin (d+1))]; congr 2; exact congr_arg (_-·) ((Maxwell.Free.phase_orientation C.labels).realInc (Nat.le_succ d) _)
     · unfold adjust at *; rw [adjusted_succ,adjusted_succ,section_rotation h, map_add, F.phase.transport.spots.filtered,hQ,← h₀.axis, map_sub ((turns C).act (d+1) s), (baseRights (H:=H) h).filtered]
     rw [← (K).fixs (Maxwell.Free.scheme_filters _) H.laws (Nat.le_succ d), adjacent_eq,hU,(V).fixs F.phase.transport.injection F.room.kernel.laws]
lemma plan_angle (hL:Adjacent F A l)(hA:∀ d,∀ᶠ i in l, obedient F H (A i) d)(d:ℕ): ∀ᶠ i in l, obedient F H (compatible F (A i)) d := by
    filter_upwards [bij F hL d, eventually_all.mpr (fun k : Fin (d+1)=> hA k.val)] with i he ht
    obtain ⟨hp,hq,hf⟩:= plan_actual F h H d (fun k hk=> ht ⟨k,Nat.lt_succ_of_le hk⟩)
    exact ⟨fun x=> by rw [compatible_at F d he,compatible_at F d he]; exact (hp x).symm,
           (compatible_at F d he _).trans hf, fun s v=> by rw [compatible_at F d he,compatible_at F d he]; exact (hq s v).symm⟩
lemma unchanged4 (hL:Adjacent F A l)(hA:∀ d:ℕ,d ≤ 4→∀ᶠ i in l, obedient F H (A i) d): ∀ᶠ i in l, compatible F (A i) 4 = A i 4 := by
  have he (d : ℕ) (hd:d ≤ 4) : ∀ᶠ i in l, adjust F (A i) d=(A i d).toLinearMap:=by
    induction d with
    | zero => exact Eventually.of_forall fun _=> rfl
    | succ d IH=>
      have hh:d<4:=hd
      filter_upwards [hA d hh.le,hA (d+1) hd,IH hh.le] with i hI hu hX; apply LinearMap.ext; intro v
      change adjusted _ _ _ _ (d+1) v=_; rw [adjusted_succ,show adjusted _ _ _ _ d _=(A i d) _ from LinearMap.congr_fun hX (peelDown C d v), map_sub]
      obtain ⟨c,hc⟩:=YM.UVNext.FreeStress.below C.labels h hh (peelDown C d v)
      rw [hc,map_smul,map_smul,map_smul,map_smul,hI.unit,(V).fixs F.phase.transport.injection F.room.kernel.laws (Nat.le_succ d),(K).fixs (Maxwell.Free.scheme_filters _) H.laws (Nat.le_succ d),hu.unit]; exact add_sub_cancel ..
  filter_upwards [he 4 le_rfl,bij F hL 4] with i hi hu
  exact LinearEquiv.ext fun v=> (compatible_at F 4 hu v).trans (LinearMap.congr_fun hi v)
end compatible
end YM.PhysMS.Frame
