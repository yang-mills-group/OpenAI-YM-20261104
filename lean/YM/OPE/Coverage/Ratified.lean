import YM.OPE.Coverage.Beads
/-! Equivariant triangular repair of the finite meters, retaining estimates by a
relative matrix tending to identity. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped Matrix.Norms.Frobenius
noncomputable section
namespace YM.OPE.Coverage
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb RG
open Next.UVStress Spec Maxwell Extra
open WeakScaling (Equipped)
open scoped ContDiff Topology BigOperators Classical
variable {G:Gauge}{F:Extraction.Order}{C:Family G}{S:Table C.book}{d D D' n n':ℕ}{μ R:ℝ}{r:ℕ→ℝ} (H:Final C F S)
set_option quotPrecheck false
local notation "Τ" => Bel C.book
variable (p:Shelf H r D n μ) (P:(Bel C.book).Hierarchy)
variable (b:∀ e,Nonempty (YM.Spin.change S e))
local notation "Hy" => H.room.kernel
local notation "Φ" => H.sector.derivatives
variable (V': DiffPlan (Bel C.book))
variable (hμ:R ≤ μ)(hR:0<R)(he:∀ e ≤ d, WeakScaling.Equipped P e n D R)(hd:d≤D)
open WeakScaling
abbrev cutNext (d:ℕ):= Nat.le_succ d
lemma adj_step_low (V : DiffPlan S) (W : DiffPlan (Free C)) (P:∀ d,(Free C).Field (d+1) →ₗ[ℂ] (Free C).Field d) (A : ∀ i, YM.Spin.change S i) (d:ℕ) (v : (Free C).Field (d+1)) :
    adjusted V W P A (d+1) v = V.rise (cutNext d) (adjusted V W P A d (P d v)) + A (d+1) (v-W.rise (cutNext d) (P d v)) := rfl
lemma adjusted_exact_low {V:DiffPlan S}{h:S.Hierarchy}{HH:(Free C).Hierarchy}{P:∀ d,(Free C).Field (d+1) →ₗ[ℂ] (Free C).Field d}{W:DiffPlan (Free C)}{A:∀ i,YM.Spin.change S i} (hf : V.Inclusions S) (hg : W.Inclusions (Free C)) (hv : V.Orientation h.spin) (hw : W.Orientation HH.spin)
    (hr : ∀ d, (∀ v, P d (W.rise (Nat.le_succ d) v)=v) ∧
      (∀ g v, P d ((Free C).mirror HH.spin _ g v) = (Free C).mirror HH.spin _ g (P d v)) ∧
      ∀ v, P d ((Free C).conj HH.spin _ v) = (Free C).conj HH.spin _ (P d v))
    (ha : ∀ d ≤ D, YM.Spin.realH h.spin HH.spin (A d))(ha':A 0 ((Free C).unit 0)=S.unit 0) :
    Exact V W h.spin HH.spin (adjusted V W P A) D := by
  let X := adjusted V W P A
  have he d v : X (d+1) (W.rise (Nat.le_succ d) v) = V.rise (Nat.le_succ d) (X d v) := by
    simp only [X,adj_step_low,(hr d).1,sub_self,map_zero,add_zero]
  constructor
  · intro d hd; induction d with
    | zero => exact ⟨(ha 0 hd).1,(ha 0 hd).2,ha'⟩
    | succ d ih =>
      obtain ⟨h₁,h₂,h₃⟩ := ih (by omega)
      refine ⟨fun g v => ?_,fun v => ?_,?_⟩
      · rw [adj_step_low,(hr d).2.1,h₁, ← hw.mirrorInc,← map_sub,(ha _ hd).1, adj_step_low,map_add,hv.mirrorInc]
      · rw [adj_step_low,(hr d).2.2,h₂,← hw.realInc,← map_sub,(ha _ hd).2, adj_step_low,map_add,hv.realInc]
      change X _ _=_; rw [← W.fixs hg HH.laws (Nat.le_succ d),he,h₃,V.fixs hf h.laws]
  intro d e hde _ v
  change X e _ = _
  induction e, hde using Nat.le_induction with
  | base => rw [W.arrival HH.laws.toSymmetric hg,V.arrival h.laws.toSymmetric hf]
  | succ e hde ih => rw [← W.transit HH.laws.toSymmetric hg hde (Nat.le_succ e),he,ih (by omega),V.transit h.laws.toSymmetric hf]
local notation "A" => fun k d=> oldChart H p d k (b d)

include hμ hR he hd p b
set_option maxHeartbeats 5000000
lemma ratify (hV : V'.Inclusions (Bel C.book))(hO : V'.Orientation P.spin)(hP : V'.Derivatives (Bel C.book)) :
    ∃ K:ℕ→∀ d,YM.Spin.change S d,
     (∀ᶠ k in atTop,Graded (Φ) V' (Hy).spin P.spin (K k) d) ∧
     (∀ e, e<d → ∀ a v,Tendsto (fun k=>(K k (e+1)).symm (p.path k • (Φ).deriv e a (K k e v))) atTop (𝓝 (V'.deriv e a v))) ∧
     ∀ e, e≤d → ∀ v,Tendsto (fun k=> (oldChart H p e k (b e)).symm (K k e v)) atTop (𝓝 v) :=by
   choose Ψ hb₁ hb₂ hb₃ using WeakScaling.retraction P V' hV hO
   have ha: Near (Φ) V' A d:= fun i hi v=> shelf_inc H p P b hμ hR he hd V' hV _ _ (by exact Nat.le_succ _) hi v
   have hnext : ∀ᶠ k in atTop,∀e ≤d,Bijective (p.maps k e):= ((eventually_all_finset (Finset.Iic d)).mpr (fun t ht=> shelf_equipment_bij H p P b hμ hR he hd t (Finset.mem_Iic.mp ht))).mono fun i hi l hl=> hi _ (Finset.mem_Iic.mpr hl)
   have hSpin : ∀ᶠ i in atTop,(∀ t:ℕ,t≤d → YM.Spin.realH ((Hy).spin) P.spin (oldChart H p t i (b t))) ∧ A i 0 ((Bel C.book).unit 0)=S.unit 0 :=by
       filter_upwards [hnext] with i hi
       refine ⟨fun t ht=> ?_, ?_⟩
       · constructor
         · intro g v;change (oldChart H p t i _).toLinearMap _= (S.mirror _ t g) ((oldChart H p t i _).toLinearMap v); erw [old_agrees H p b i t (hi t ht)]; exact (p.realism i t (ht.trans hd)).reflects g v -- realism spin proof irrel
         intro v; change (oldChart H p t i _).toLinearMap _= (S.conj _ t) ((oldChart H p t i _).toLinearMap v); erw [old_agrees H p b i t (hi t ht)]; exact (p.realism i t (ht.trans hd)).bars v
       change (oldChart H p 0 i _).toLinearMap _=_;rw [old_agrees H p b i 0 (hi _ (Nat.zero_le d))]; exact p.fixed i
   let K:= rotateChart (Φ) V' Ψ A
   refine ⟨K,?_,?_,fun e he v=> relative (P:=Ψ) ha he v⟩
   · have hbij := (eventually_all_finset (Finset.Iic d)).mpr (fun j hj=> eventually_unit (P:=Ψ) ha (Finset.mem_Iic.mp hj))
     filter_upwards [hbij,hSpin] with k hk hs
     have hEq(e:ℕ)(hd:e ≤ d)(v:(Bel C.book).Field e) : (rotateChart (Φ) V' Ψ A k e v)=(adjusted (Φ) V' Ψ (A k) e v):= rotate_eq (A':= fun k e=> oldChart H p e k (b e)) (hk e (Finset.mem_Iic.mpr hd)) v
     have hA:= adjusted_exact_low (P:=Ψ) (h:=Hy) (HH:=P) H.phase.transport.injection hV H.phase.transport.rights hO (fun d=>⟨hb₁ d,hb₂ d,hb₃ d⟩) hs.1 hs.2
     constructor
     · intro e he; change (∀ (g:Signed) (v:(Bel C.book).Field e),K k e ((Bel C.book).mirror _ _ g v)= S.mirror _ _ g (K k e v)) ∧ (∀ v,K k e ((Bel C.book).conj _ e v)= S.conj _ e (K k e v)) ∧ K k e _=_
       simpa only [K,hEq e he] using hA.1 _ he -- `_ _=_` lhs has placeholders ambiguous; explicit next if fails
     · intro e f hf hf' v;change K k f _=(Φ).rise hf (K k e _); simpa only [K,hEq e (hf.trans hf'), hEq f hf'] using hA.2 e f hf hf' v
   intro e hE a v
   refine transformed (d:=e) (A':= fun k e=> oldChart H p e k (b e)) (fun i=>p.path i • (Φ).deriv e a) (V'.deriv e a) (shelf_diff H p P b hμ hR he hd V' hP hE a) (fun x=>relative ha (P:=Ψ) hE.le x) (fun x=>relative (P:=Ψ) ha hE x) v
end YM.OPE.Coverage
