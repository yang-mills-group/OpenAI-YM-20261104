import YM.OPE.Compatible.Assemblage.Measure
/-!
# Cropping and recharging through conflicts

Continue with an *extension*, not necessarily matching unwanted modes. Important that
P≍Q preserves all the prices on the *actual* terms read at this step. Includes Hover
for using true integrals also with the artificial extension. Does not charge that
finite-integrability bound to the order of the array.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
set_option linter.unusedSectionVars true
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V I J X N : Type} [Fintype V][DecidableEq V] [Fintype I][DecidableEq I]{G:Gauge}{n:Side}
    {R:Rep G n}{d e c a w η α σ T Q b τ : ℝ}
-- full Bud below once. Could alternatively use a Quotient algebra.
structure Guard (B:Census V) where
    safe : B.Mode→ Prop
    quiet : safe B.quiet
    fire v : safe (B.fire v)
    sub {s t:B.Mode}: s.val⊆t.val→ safe t → safe s
namespace Guard
variable {B:Census V} (χ:Guard B)
def Saw (v w:Poly B):Prop:= ∀ s,χ.safe s→ v.part s=w.part s
def Filtered (v w:X→Poly B):Prop:= ∀ U, χ.Saw (v U) (w U)
variable {q p r t:Poly B}
lemma reflects {V : Type} [Fintype V] [DecidableEq V] {B : Census V} (χ : Guard B) (p:Poly B):χ.Saw p p:= fun _ _=>rfl
lemma Saw.add {V : Type} [Fintype V] [DecidableEq V] {B : Census V} (χ : Guard B) {q p r t : Poly B} (h:χ.Saw p q)(he:χ.Saw r t): χ.Saw (p+r) (q+t) :=fun s hs=> congr_arg₂ (·+·) (h s hs) (he s hs)
lemma Saw.mul {V : Type} [Fintype V] [DecidableEq V] {B : Census V} (χ : Guard B) {q p r t : Poly B} (h:χ.Saw p q)(he:χ.Saw r t): χ.Saw (p*r) (q*t):=by
    intro s hs; rw [Poly.part_mul,Poly.part_mul]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=> ?_
    split; next hv=> rw [h i (χ.sub (hv.2 ▸ subset_union_left) hs), he j (χ.sub (hv.2 ▸ subset_union_right) hs)]
    rfl
lemma Saw.scale {V : Type} [Fintype V] [DecidableEq V] {B : Census V} (χ : Guard B) {q p : Poly B} (h:χ.Saw p q)(x:ℂ): χ.Saw (x • p) (x • q):=fun i hi=> congr_arg (x*·) (h i hi)
lemma Saw.power (h:χ.Saw p q)(k:ℕ): χ.Saw (p^k) (q^k):=by induction k with
    | zero=> simpa only [pow_zero] using χ.reflects 1
    | succ k ih=> simp_rw [pow_succ]; exact ih.mul χ h
lemma sums {V X : Type} [Fintype V] [DecidableEq V] {B : Census V} (χ : Guard B) {f g:X→Poly B}(s:Finset X)(h:∀ i∈s,χ.Saw (f i) (g i)): χ.Saw (∑ i∈s,f i) (∑ i∈s,g i):=by
    intro i hi; rw [Poly.part_sum,Poly.part_sum]; exact sum_congr rfl fun _ he=>h _ he _ hi
lemma prod {f g:X→Poly B}(s:Finset X)(h:∀ i∈s,χ.Saw (f i) (g i)): χ.Saw (∏ i∈s,f i) (∏ i∈s,g i):=by
    induction s using Finset.induction_on with
    | empty=> simp only [prod_empty]; exact χ.reflects _
    | @insert i s hi ih=> simp_rw [prod_insert hi]; exact Saw.mul χ (h i (mem_insert_self ..)) (ih fun i hi=>h i (mem_insert_of_mem hi))
lemma Saw.pass (h:χ.Saw p q): χ.Saw p.pass q.pass:=χ.sums _ (fun i _=>Saw.scale χ (Saw.power χ h i) _)
lemma swab {F F':Support n→ Config G n→Poly B}{K K':Box n→ Config G n→Poly B} (φ:V→ Config G n→ℂ)(k:V→ Res G n)
    (h:∀ i,χ.Filtered (F i) (F' i))(he:∀ i,χ.Filtered (K i) (K' i)): χ.Filtered (restore R φ k F K) (restore R φ k F' K'):=by
    intro U; apply Saw.scale; apply Saw.mul; apply Saw.pass; exact Saw.add χ (χ.reflects _) (χ.sums _ (fun i _=> h i U)); apply χ.sums; intro i _; unfold grid; split; next hv => exact χ.prod _ (fun i _=>Saw.add χ (χ.reflects _) (he i U))
    next=> exact χ.reflects _
lemma brought {V : Type} [Fintype V] [DecidableEq V] {G : Gauge} {n : Side} {B : Census V} (χ : Guard B) {S':Side}{T:StepData S' n}{g f:Config G n→Poly B}{η:ℝ}(h:χ.Filtered g f)(hg:Integrable g (prior G _))(hf:Integrable f (prior G _))(he:T.IsKernel η G): χ.Filtered (T.push η g) (T.push η f):=fun i p hp=>(congr_fun (push_get he hg p) i).trans ((congr_arg (fun f:Config G n→ℂ=> T.push η f i) (funext fun U=>h U _ hp)).trans (congr_fun (push_get he hf p) i).symm)
variable [Fintype J]
variable {W W':V→ℝ} {F:J→ Config G n→Poly B}{S:J→Support n}{r:ℕ}{o:V→Site n}{T:ℝ}
-- output mode gain allowed when *safe.*
def Gates (o:V→Site n)(r:ℕ)(W W':V→ℝ)(e:ℝ) := ∀ (i:B.Mode),2 ≤ i.val.card→χ.safe i → ∀ s:Support n,i.val.image o⊆s → Poly.toll W' i ≤ Poly.toll W i * Real.exp (e*coverNumber r s)
def cropped (p:Poly B):Poly B:=Poly.inject (fun i=> if χ.safe i then p.part i else 0)
lemma crops {V : Type} [Fintype V] [DecidableEq V] {B : Census V} (χ : Guard B) (p:Poly B):χ.Saw p (χ.cropped p):= fun _ hi=>(if_pos hi).symm
lemma finer {V : Type} [Fintype V] [DecidableEq V] {G : Gauge} {n : Side} {τ : ℝ} {B : Census V} (χ : Guard B) {o : V → Site n} {s:Support n}{F: Config G n→Poly B}(h:Borne o s F τ) : Borne o s (χ.cropped ∘ F) τ:=by
    refine ⟨fun U V hx hy=> congr_arg χ.cropped (h.home U V hx hy),fun i U=>congr_arg χ.cropped (h.turns i U),fun i=>?_,fun U i hi=>?_⟩
    · change Measurable (fun U=> if χ.safe i then _ else _); split; exact h.me _; exact measurable_const
    change (if χ.safe i then _ else _)=0; split;exact h.scope U i hi; rfl
lemma cut_zero {V : Type} [Fintype V] [DecidableEq V] {B : Census V} (χ : Guard B) : χ.cropped 0=0:=by ext i; change (if _ then (0:Poly B).part i else 0)=0; simp only [Poly.part_nil,ite_self]
lemma cut_burn {F:Config G n→Poly B}{s}(h:Burns o s F τ): Burns o s (χ.cropped ∘ F) τ := ⟨χ.finer h.toBorne,fun i hi=>h.permits i (fun H=>hi ((congr_arg _ H).trans χ.cut_zero)),fun i=> ((χ.crops (F i)) _ χ.quiet).symm.trans (h.sil i)⟩
lemma cut_flow {F:Config G n→Poly B}{s}(h:Accent.Flow o s F τ):Accent.Flow o s (χ.cropped ∘ F) τ:=⟨χ.finer h.toBorne, fun i hi=>h.permits i (fun H=>hi ((congr_arg _ H).trans χ.cut_zero))⟩
lemma cut_rise {V : Type} [Fintype V] [DecidableEq V] {B : Census V} (χ : Guard B) {F:Poly B}(h:rises F): rises (χ.cropped F):=by
    intro i hi; change (if χ.safe i then _ else _ ) ≠ 0 at hi; split at hi; exact h i hi; contradiction
lemma croptude {F:Support n→ Config G n→Poly B}{K:Box n→ Config G n→Poly B}(h:Carton o F K τ) : Carton o (fun i=>χ.cropped ∘ F i) (fun j=>χ.cropped ∘ K j) τ :=by
   refine ⟨fun i=> ⟨cut_burn χ (h.exp i).1,fun U=>cut_rise χ ((h.exp i).2 U)⟩,fun i=> ⟨cut_flow χ (h.flag i).1,fun U=>cut_rise χ ((h.flag i).2 U)⟩⟩
lemma cut_tow {V J : Type} [Fintype V] [DecidableEq V] {G : Gauge} {n : Side} {d e τ : ℝ} {B : Census V} (χ : Guard B) [Fintype J] {W W' : V → ℝ} {F : J → Config G n → Poly B} {S : J → Support n} {r : ℕ} {o : V → Site n} {T : ℝ} (h:Towed W S F r (d+e) T)(hw:∀ i,0<W i)(_hw':∀ i,0<W' i)(ht:∀ i,Borne o (S i) (F i) τ)(hr:∀ i U,rises (F i U))(hx:χ.Gates o r W W' e): Towed W' S (fun i=>χ.cropped ∘ F i) r d T:=by
   obtain ⟨a,-,hA,h⟩:=h; let f (i:J):=Real.exp (e*coverNumber r (S i))*a i; have ha(i):= (h i|>.fares hw).1
   refine ⟨f,Summable.of_finite,fun j=>?_,fun i=>?_⟩
   · apply Extra.Multi.Budget.mono (hA j) _ _ le_rfl
     · intro j;split; next=> exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (ha _)) (Real.exp_nonneg _)
       next=>rfl
     intro i; split; next=> unfold f;simp only [add_mul,Real.exp_add]; apply le_of_eq; ring
     next=> rfl
   obtain ⟨u,hu,hu',hv⟩:= h i
   let p(j:B.Mode):= 2 ≤ j.val.card∧χ.safe j∧j.val.image o ⊆ S i; let b(j:B.Mode):= if p j then u j else 0
   refine ⟨b,fun j=>?_,fun U j=> ?_,?_⟩
   · change 0≤ if p j then _ else _; split; exact hu _; rfl
   · change ‖ite (χ.safe j) _ _‖ ≤ if p j then _ else _; by_cases hp:p j; rw [if_pos hp, if_pos hp.2.1]; exact hu' U j
     rw [if_neg hp]; split; next he => rw [show (F i U).part j=0 from (Classical.byContradiction fun H=> hp ⟨hr _ _ j H,he,(ht i).place _ _ H⟩),norm_zero]
     next=> rw [norm_zero]
   let P:= Real.exp (e*coverNumber r (S i)); refine le_trans ?_ (mul_le_mul_of_nonneg_left hv (Real.exp_nonneg _)); unfold wordsPrice; rw [mul_sum]; refine sum_le_sum (fun j _=>?_); unfold b; split
   next hp=> exact (mul_le_mul_of_nonneg_right (hx j hp.1 hp.2.1 (S i) hp.2.2) (hu j)).trans_eq (by ring)
   next hp=> rw [mul_zero]; exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (Poly.worth hw j).le (hu j))
end Guard

lemma restore_hover {Y:Census V} {o:V→Site n}{H: Support n→ Config G n→Poly Y}{K:Box n→ Config G n→Poly Y}{W:V→ℝ} {g:V→ Config G n→ℂ}{k:V→ Res G n}
  (h:R.Lawful σ c Q b w)(ht:Carton o H K R.p.threshold)(hv:Towed W id H R.p.B e a)(hU:Towed W Prod.fst K R.p.B e a)(hw:∀ i,0<W i)(hf:∀ i,Envelope (g i))(hk:∀ i j,Envelope (k i j)): Hover (restore R g k H K):=by
    apply expenses h
    · intro i; apply Hover.plus (Hover.plus ?_ ?_) (flight_grams (fun i=>(ht.flag i).1.toBorne) hU _)
      · exact flight_grams (fun i=>(granular R.activities R.p Y (o:=o) h.labels i).toBorne) (vacant _ _ Y h.labels _ hw) i
      exact Hover.many _ (fun j _=>hover_cast (hk _ _) _)
    apply Hover.plus (Hover.many _ (fun i _=>hover_cast (hf i) _)); exact Hover.many _ fun i _=> flight_grams (fun i=>(ht.exp i).1.toBorne) hv _

namespace Guard
variable {P:Config G n→Poly (Names V I)}(χ:Guard (Names V I)){V₀:V}{g:V×I→ Config G n→ℂ}{k:V×I→ Res G n}{b':V→Motion}{X':V→Site n}{B':V→Equiv.Perm V}
  {o:V×I→Site n}{A A':V×I→ℝ}
-- framing and body start upper ranks in SAME copy.
structure Chordal (V₀:V)(B:V→Equiv.Perm V) : Prop where
   there i:i≠V₀ → ∀ j:(Names V I).Mode, Focused V₀ j → (χ.safe j ↔ χ.safe (drum (B i) j))
lemma memorial (h:Serves R g k P V₀ b' X' B' o A (d+e) a)(hc:Chordal χ V₀ B')(hz:R.Lawful σ c Q b w)(hv:∀ i,Envelope (g i))(hF:∀ i j,Envelope (k i j))(hw:∀ i,0< A i)(ht:∀ i,0<A' i)(he:χ.Gates o R.p.B A A' e) :
    ∃ Υ : Config G n→Poly (Names V I), Integrable Υ (prior G _) ∧ χ.Filtered P Υ∧ Serves R g k Υ V₀ b' X' B' o A' d a:=by
   obtain ⟨X,Y,hp,hX,hY,hH,rfl⟩:=h
   let X' i:=χ.cropped∘X i; let Y' i:=χ.cropped ∘Y i; have hh:= χ.croptude hp
   have hX':Towed A' id X' R.p.B d a:= χ.cut_tow hX hw ht (fun i=>(hp.exp i).1.toBorne) (fun i=>(hp.exp i).2) he; have hY':Towed A' Prod.fst Y' R.p.B d a:=χ.cut_tow hY hw ht (fun i=>(hp.flag i).1.toBorne) (fun i=>(hp.flag i).2) he
   let f:= restore R g k X' Y'
   refine ⟨f,Hover.legible f (restore_hover hz hh hX' hY' ht hv hF) _,χ.swab _ _ (fun _ _U=> χ.crops _) (fun _ _U=>χ.crops _), X',Y',hh,hX',hY',?_,rfl⟩
   have hh (i:V)(hi:i≠V₀){p q:Poly (Names V I)}(h:Harm V₀ (B' i) (b' i) p q): Harm V₀ (B' i) (b' i) (χ.cropped p) (χ.cropped q):=by
       intro x hx; by_cases ht:χ.safe x; · exact ((χ.crops q) _ ((hc.there i hi x hx).mp ht)).symm.trans ((h x hx).trans (congr_arg _ ((χ.crops p) _ ht)))
       rw [show (χ.cropped p).part x=0 from if_neg ht,show (χ.cropped q).part (drum (B' i) x)=0 from if_neg (fun he=> ht ((hc.there i hi x hx).mpr he)),scalar_z]
   exact fun i hi=> ⟨(hH i hi).1,fun U=> ⟨fun j=>hh i hi ((hH i hi).2 U|>.1 j),fun j=>hh i hi ((hH i hi).2 U|>.2 j)⟩⟩
end Guard
end YM.MergeProof.Ribbons.ManyCopies
