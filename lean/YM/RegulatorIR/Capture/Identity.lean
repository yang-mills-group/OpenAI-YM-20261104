import YM.RegulatorIR.Capture.Catcher

/-!
# Terminal in V0

h=0 coordinate does not require inverting an arbitrary pivot; Fk inverse
calibration on identity pivot is 1 by construction. On-shell identification
of other sectors cannot be read using this simplification. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Capture
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles Sources Centered Labels Source Aperture
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W I J X Y A B: Type}{q u b p a i j e k d m r:ℕ}{M: W→ℕ}{n:Page M→Side}{L:Meter W}{D:Choice M}
section Unit

def atomU (X:Type): Orders X:= Pi.single 0 (Pi.single 0 1)
lemma scalar_h {P:Orders X}(h:∀ e i, 0 < i → P e i=0) (K:Layer X X)(V): markHeat K V P=fun j=> if j=0 then P else 0:=by
 ext1 j; induction j using Nat.strong_induction_on with
 | _ j ih=>
    cases j with
    | zero=>rw [markHeat_first,if_pos rfl]
    | succ j=>
       rw [if_neg (by omega)]; ext1 p; ext1 i; rw [markHeat_next]; have he (t:ℕ)(hh:t≤j) e v (hg:0<v) : markHeat K V P t e v=0:=by rw [ih t (by omega)];split; exact h e v hg; rfl
       have hv: heating K (markHeat K V P j p) i=0:= by by_contra hp; exact heating_comes hp (he j le_rfl _ _ (by omega))
       have ht : drift K (markHeat K V P) V j p i=0:=by by_contra hp; obtain ⟨k,l,u,v,a,b,g,_ ,_ ,hz,_ ⟩:= joins_come hp; exact hz (he k (by omega) u _ (by omega))
       rw [hv,ht];simp
lemma transferUnit {P :ℝ}{X Y A B:Type}{E:Deck P X A}{F:Deck P Y B}(J:GridStep E F)(V): J.each m V (atomU X)= atomU Y:=by
 let p:=Cluster.present (firstChannel E F).native (atomU X); let Q:= endHeat m J.line (logHeat J.line (J.jVac V) false) p
 have hz {X:Type}(i r) (h:i≠0 ∨ r≠0) : atomU X i r=0:=by rcases h with h|h;rw [atomU,Pi.single_eq_of_ne h]; rfl; by_cases hv:i=0; rw [atomU,hv,Pi.single_eq_same,Pi.single_eq_of_ne h]; rw [atomU,Pi.single_eq_of_ne hv];rfl
 have hp i r (h:i≠0∨r≠0): p i r=0 := by unfold p present; rw [hz i r h]; ext;simp [offer,Stalk.collect]
 have ht: Q=p:=by ext1 i;ext1 j;unfold Q endHeat heated;rw [scalar_h (fun i k h=>hp i k (Or.inr h.ne'))]; rw [sum_eq_single_of_mem 0 (by simp)]; simp; intro b hb h;simp [h]
 ext1 i;ext1 r;change crop _ (draft _ (Q i r))=_;rw [ht]; by_cases hc:i≠0∨r≠0
 · rw [hp i r hc,hz i r hc]; apply Eq.trans (b:=crop _ (0:Packet _ r)); swap;rfl
   rw [show draft _ (0:Packet _ r)=0 from ?_]
   simpa only [zero_smul] using scaleDraft (r:=r) 0 J.driftL 0
 obtain ⟨rfl,rfl⟩:= show i=0∧r=0 from by simpa using hc
 rw [show draft J.driftL _=(p 0 0) from ?_]; swap
 · change symmetry _=_;unfold symmetry;simp;rfl
 ext1 t; let a:Tuple (X⊕Y) 0:= acrossT (lastChannel E F).native t; change p 0 0 a= atomU Y 0 0 t; rw [show a=acrossT (firstChannel E F).native (Fin.elim0 : Tuple X 0) from Subsingleton.elim ..]; unfold p present; rw [offer_eq]; simp [atomU]

lemma only_unit_label (L:Labels.Frame G 0)(i:L.Index): i=0:=by
 by_contra! he
 let v:=L.basis i; have hv:= v.property.1; change v.val ∈ Labels.limited G 0 at hv; rw [limited,MvPolynomial.mem_restrictSupport_iff] at hv; let c:= MvPolynomial.coeff 0 v.val
 have ht:L.basis i=c • L.basis 0:=by
    rw [L.starts_unit];apply Subtype.ext; change v.val=c • (1:Pol G); ext1 h; by_cases hh:h=0; simp [hh,c]
    simp only [MvPolynomial.coeff_smul,MvPolynomial.coeff_one]; simp [Ne.symm hh]; by_contra! hm; have he:= hv (MvPolynomial.mem_support_iff.mpr hm); change Labels.height h≤0 at he
    obtain ⟨x,hx⟩:= Finset.nonempty_iff_ne_empty.mpr (show h.support≠∅ from fun ht=> hh (Finsupp.support_eq_empty.mp ht))
    have hh:0<h x:= Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hx)
    have hz:0<Labels.height h:= by unfold Labels.height; rw [Finsupp.weight_apply]; exact lt_of_lt_of_le (c:=h.sum _) (show 0<h x*generation x from Nat.mul_pos hh (by unfold generation;omega)) (Finset.single_le_sum (f:=fun x=> h x*generation x) (fun _ _=> Nat.zero_le _) hx)
    omega
 have hv:=congr_arg (fun v=> L.basis.repr v i) ht; simp [he] at hv
lemma stroke_sum {F:Labels.Frame G 0} (x:Stroke F) : nu x=0:= by have h:= combo x;omega
end Unit

variable {S:Heir n G}(R:Reel S)(T:S.Accounts)
-- `unitArc` constant test, only joint label. propagate its $N_j$ coefficients. This
-- computes $M^0$ representation (inverse identity). Ext fields passed separately.

def resetO (_m:ℕ): Sample (Foot G):= fun φ=> φ 0 • atomU _
def unitArc : ∀ (_:Page M), Sample (Foot G):= Halo.seriesC (X:=fun _=> Sample (Foot G)) (fun _=>resetO 0) fun w=>fun b=>sprink R T w b 0
lemma settles : ∀ w,unitArc R T w 1=atomU (Foot G):=by
 refine Page.proves (fun w=> ?_) ?_
 · change (1:ℝ) • _=_; rw [one_smul]
 intro w hw
 let L:=(R.steps w).patch.L; unfold unitArc; rw [Halo.laterC]; let U:= unitArc R T w.prev; let X:= atomU (Foot G)
 change tally L 0 • (∑ i:Site L,(S.frames w).each _ _ (rebaseO _ (U (calling L 1 i))))= _
 have hQ (i : Cover): rebaseO i X=X:=by
    ext1 e;ext1 p;ext1 x; change X e p (_ : Tuple _ _)= X e p x; cases Nat.eq_zero_or_pos p with
    | inl h=>subst p; rw [Subsingleton.elim (onPath _ _) x]
    | inr h=> by_cases h':e=0 <;> simp [X,atomU,h',Pi.single_eq_of_ne (by omega:p≠0)]
 have hz(i:Site L): (S.frames w).each 0 (T.bulk w.prev) (rebaseO (Lattice.lift i) (U (calling L 1 i)))= X:=by rw [show calling L 1 i=1 from rfl,show U 1=X from hw,hQ]; exact transferUnit ..
 rw [Finset.sum_congr rfl (g:=fun _=>X) (fun i _=>hz i),sum_const,card_univ,Lattice.site_card]; ext1 e; ext1 p;ext1 y; change tally L 0*(L.val^4 • (X e p y))=X e p y;unfold tally display; simp

variable (Z:(portraitR T).Report m) (C J':Choice M)(h:C.age≤J'.age)
-- exact grade 0 representative: project to constant potential and constant test at j on the complete transferred kernel. T^0 inverse factor identity. T.prim [not source-dependent].

def birth (w:W):Page C.after.spans:= ⟨w,J'.age w-C.age w,Nat.sub_le_sub_right (J'.young w) _⟩
include h in
lemma rebirth (w:W): C.after.page (birth C J' w)=J'.choose w:=by simp [Era.page,birth, Choice.after, Choice.choose]; rw [Nat.add_sub_of_le (h w)]

def vanishMark (Q: Sample (Foot G))(i):= note (Q 1 i 0)
def grouped (w:W)(e:ℕ):ℝ:= vanishMark (catcher R T Z C (birth C J' w)) e
include h
lemma coherent (P:Milieu S T k p L) (H: ∀ w l, Nonempty (Store (fun x=>Z.main (leafX w x)) (Metric.closedBall 0 l) p)) (X₀: ∀ i x t,swing Z i x t)(he:e≤p) (w:W): grouped R T Z C J' w e= diffuse S T Z J' e w:=by
 unfold grouped vanishMark; rw [captured R T Z P H X₀ _ 1 continuous_const e he,rebirth _ _ h]
 unfold collected note weighsC
 simp_rw [Pi.one_apply,one_mul]; rfl
end YM.RegulatorIR.Capture
