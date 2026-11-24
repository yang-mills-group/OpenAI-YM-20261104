import YM.QuadraticLocal.Germ.Smalt
/-!
# qlocal — recovering complex costs coherence on test geometry-
 FullBudget Hook. Maintains norm scale and full powers, shoes. Centers root uses. Stamp all v.
 No rate loss in this projection.Cert.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Affinity.Smalt
open Function Filter Finset Lattice Wilson RG Marker MeasureTheory Push Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V:Type}[DecidableEq V]{R:Census V}{G:Gauge}{c:Side}
variable {E: V→Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
variable (R) (v:V){F G':(∀ i,E i)→Poly R}
variable (A:∀ i,Set (E i))(K:∀ i, Submodule ℂ (E i))
local notation "Y"=> Full (E:=E)
local notation "Iᴍ"=> Complex.I
variable {R A K}
local notation "m"=> mean R v
local notation "q"=> ModeWeight.turn R (shadow v)
lemma mean_sum (t:Y): m (fun t=> F t+G' t) t=m F t+m G' t:=by
    unfold mean; rw [map_add]; dsimp only; simp_rw [smul_add]; abel
lemma mean_nil (t:Y): m (fun _=>0) t=0:=by unfold mean; simp
lemma mean_shine (t:Y): m (fun _=>1) t=1:=by unfold mean; rw [ModeWeight.roll]; ext q'; simp only [Poly.part_smul,Poly.part_plus,Poly.one_part]; ring
lemma mean_const (t:Y)(c:ℂ): m (fun t=> c • F t) t=c • m F t:=by
    unfold mean; rw [map_smul]; dsimp only; rw [←smul_add,smul_comm]
open RG3.Held
lemma mean_mul (t:Y)(h: Published (K:=ℝ) E F) (he: Published (K:=ℝ) E G'):
    m (fun t=> F t*G' t) t=m F t*m G' t:=by
    ext i; rw [part, Poly.part_mul]; simp_rw [Poly.part_mul,solo_sum]; refine sum_congr rfl fun j _=> sum_congr rfl fun k _=> ?_
    split_ifs with h'
    next=> rw [part,part,← binds₂ v (h j) (he k) h'.1 t]; exact congr_arg (fun (s:Finset V)=> solo v (fun t=> (F t).part j* (G' t).part k) s t) h'.2.symm
    next=> simp [solo]
lemma mean_roll (t:Y) {ι:Type*}(S:Finset ι)(F:ι→Y→Poly R): m (fun t=>∑ i∈S,F i t) t=∑ i∈S,m (F i) t:= by
   induction S using Finset.induction with
   | empty=> simp_rw [sum_empty]; exact mean_nil _ t
   | insert i s hi ih=>simp_rw [sum_insert hi]; rw [mean_sum, ih]
lemma mean_bind (t:Y){ι:Type*}(S:Finset ι) (F:ι→Y→ Poly R)(h:∀ i∈S, Published (K:=ℝ) E (F i)): m (fun t=>∏ i∈S,F i t) t=∏ i∈S,m (F i) t:= by
   induction S using Finset.induction with
   | empty=> simp_rw [prod_empty]; exact mean_shine _ t
   | insert i s hi ih=> simp_rw [prod_insert hi]; have he(j:ι)(he:j∈s): Published (K:=ℝ) E (F j):= h _ (mem_insert_of_mem he); rw [mean_mul v t (h i (mem_insert_self ..)) (Published.prod s F he), ih he]
lemma mean_pow (t:Y)(h: Published (K:=ℝ) E F) (i:ℕ): m (fun t=> F t ^ i) t= m F t ^i:= by
   induction i with
   | zero=> simp_rw [pow_zero]; exact mean_shine _ t
   | succ i hi=>simp_rw [pow_succ]; rw [mean_mul v t (h.power i) h, hi]
lemma mean_pass [Fintype V](t:Y) (h: Published (K:=ℝ) E F): m (fun t=>Poly.pass (F t)) t= Poly.pass (m F t):= by
   unfold Poly.pass; rw [mean_roll]; apply sum_congr rfl; intro i _; rw [mean_const, mean_pow v t h i]
lemma mean_apply {I:Type*}(f:I→Y→ Poly R)(h: ∀ x,Summable (fun i=>f i x))(t:Y):
    HasSum (fun i=>m (f i) t) (m (fun t=> ∑' i,f i t) t):=by
   -- CI complex μ
   have hp:= (h t).hasSum; have he:= (h (spin v t)).hasSum; let H:= he.mapL q; exact (hp.add H).const_smul (2:ℂ)⁻¹
-- projection commutes with actual push. assumption shifted scale Integrable at INPUT only. Need actual IsKernel. No support bounds used here.
variable {S T : Finset V}{B:BudgetPoint}{P:Rep G c} {o: V→ Site c}
variable (X:V→Support c)
lemma mean_push [Fintype V] {n:Side}(S:StepData n c) {β:ℝ}(hf:S.IsKernel β G)(A:Y→ Config G c→Poly R)(h:∀t, Integrable (A t) (prior G c))(t:Y)(x:Config G n): m (fun t=>S.push β (A t) x) t=S.push β (fun z=>m (fun t=> A t z) t) x := by
   let q0:Poly R→L[ℝ] Poly R:= (q).restrictScalars ℝ; let F:= A (spin v t); unfold mean; have he := ModeWeight.advance R q0 F hf (h (spin v t))
   rw [show q _=S.push β (q0 ∘ F) x from congr_fun he x,← show S.push β (A t + q0 ∘ F) x= S.push β (A t) x+ S.push β (q0 ∘ F) x from congr_fun (StepData.push_add hf _ _ (h t) (q0.integrable_comp (h _))) x]; unfold StepData.push; simp_rw [← integral_smul]; refine integral_congr_ae (ae_of_all _ fun u=>?_); exact smul_comm ..

private lemma letterSolo {Q:Type}[RCLike Q][NormedAlgebra Q ℂ][∀ i,Module Q (E i)](i:R.Mode){f:Y→ℂ}(h: Letter Q E i.val f): Published (K:=Q) E (fun t=> Poly.send i (f t)):=by
    intro j; simp_rw [Poly.part_send]; split; next he=> subst j; exact h
    next=> exact Letter.still
lemma entire {Q:Type}[RCLike Q][NormedAlgebra Q ℂ][∀ i,Module Q (E i)]{s:Finset V}{f:Y→ℂ} (h:Letter Q E s f): Affinity.Eligible (fun i=> (⊥: Submodule Q (E i))) s f:= by
    refine ⟨h,fun i hi t ht=>?_⟩
    rw [Submodule.mem_bot] at ht; have hx:= h.scale t i hi 0 (t i); simpa only [zero_smul,← ht,Function.update_eq_self] using hx
lemma mean_identity (t:Y)(h:Published (K:=ℂ) E F): m F t=F t:=by
    ext i; rw [part]; exact congr_fun (Smalt.Eligible.fixed v (entire (h i))) t -- typo variable

open Next.Foundations Push.Corrected
variable {ι:Type} (L:Gallery (Full (E:=E)) ι o P R)
-- fusing real output **same address**. No merging before.
private def value (t:Y)(i:ι):Config G c→ ℂ := (2:ℂ)⁻¹ • (L.E.nominal t i+ meter v (L.E.mode i).val • L.E.nominal (spin v t) i )
private def lights : Lamps (Full (E:=E)) ι G P.p o R:= { L.E with
   nominal:= value v L
   legal:= fun t i=> regular_smul _ (regular_add (L.E.legal _ i) (regular_smul _ (L.E.legal _ i)))
   pure:= fun t i U h=> by
     unfold value; dsimp only [Pi.add_apply,Pi.smul_apply]; rw [L.E.pure t i _ h,L.E.pure _ i U h] }
local notation "L*"=> lights v L
private lemma color i t U: (L*).nominal t i U=solo v (fun t=> L.E.nominal t i U) (L.E.mode i).val t:=rfl
private lemma hardPlate i (t:Y): Width.LocalCharge P.p o ((P.activities.forced i).support) (fun U=> mean R v (fun t=> L.K.hard t i U) t):=by
   let x:= L.K.locality t i; let g:= L.K.locality (spin v t) i; unfold mean; refine ⟨fun u U=> ?_, ?_, fun U V hx hp=> ?_, fun U j hj y hy=>?_⟩
   · dsimp only; rw [x.gauge u U,g.gauge u U]
   · exact (x.borel.add ((q).continuous.measurable.comp g.borel)).const_smul (2:ℂ)⁻¹
   · dsimp only; rw [x.reads U V hx hp,g.reads U V hx hp]
   rw [Poly.part_smul,Poly.part_plus,ModeWeight.scale] at hj; by_contra hv; exact hj (by rw [not_not.mp (fun he=>hv (x.carry U j he y hy)),not_not.mp (fun he=>hv (g.carry U j he y hy)),mul_zero,add_zero,mul_zero])
def filterHard : Hard (Full (E:=E)) P.p (P.activities.forced) (P.activities.K) o R where
    hard t i U:= mean R v (fun t=> L.K.hard t i U) t
    locality t i:= hardPlate v L i t
    charged t i U h:= by by_contra hv; apply h; unfold mean; dsimp only; rw [not_not.mp ((mt (L.K.charged t i U)) hv),not_not.mp (mt (L.K.charged _ i U) hv),map_zero,add_zero,smul_zero]; -- simplification
    quiet t i U:= by rw [part]; unfold solo; simp_rw [L.K.quiet,without v (show v ∉R.quiet.val from Finset.notMem_empty v)]; ring
def circular : Gallery (Full (E:=E)) ι o P R:= ⟨lights v L, filterHard v L⟩
local notation "C"=> circular v L
private lemma spiral t i U: (L*).light t i U = solo v (fun t=> L.E.light t i U) (L.E.mode i).val t:=by
   unfold solo Lamps.light; rw [show (L*).ground i=L.E.ground i from rfl,show (L*).clear i=L.E.clear i from rfl]; split
   next hc=> exact color ..
   next h=> by_cases he:Healthy P.p.threshold (L.E.ground i) U
            · simp_rw [masked_eq _ _ _ _ he]; exact color ..
            simp_rw [masked_ne _ _ _ _ he]; ring

variable (K)
-- U inventory from Loc.ports; no minim.H.World.
structure Printed (T:Finset V)(L:Gallery (Full (E:=E)) ι o P R) : Prop extends Adult X (imported K) L where
   day i U : Mixed K T (L.E.mode i).val (fun t=> L.E.nominal t i U)
   night i (q':R.Mode) U : Mixed K T q'.val (fun t=> (L.K.hard t i U).part q')
variable {K X}
lemma ink (h:Adult X (imported K) L): Printed K X ∅ L:= ⟨h, (fun i U=>honestBlank (h.regular _ _)),fun i q' U=>honestBlank (h.hard _ _ _)⟩
lemma exfil (h:Adult X K L): Adult X (imported K) L := { house:= h.house, regular:= fun i U=>Eligible.faded (h.regular ..), hard:= fun i q' U=>Eligible.faded (h.hard ..),stalk:=h.stalk }
lemma reveal [Fintype V](h:Printed K X univ L): Adult X K L:= ⟨h.house,fun i U=>recovered (h.day i U),fun i q' U=> recovered (h.night i q' U), h.stalk⟩
lemma again (h:Printed K X S L): Printed K X (insert v S) (circular v L):=by
    have ht i U: Mixed K (insert v S) (L.E.mode i).val (fun t=>(L*).nominal t i U) := by simp_rw [color]; exact sunrise v (h.day i U)
    have hv i q' U: Mixed K (insert v S) q'.val (fun t=> ((C).K.hard t i U).part q') := by unfold circular filterHard; dsimp only; simp_rw [part]; exact sunrise v (h.night i q' U)
    refine ⟨⟨h.house,(fun i U=>(ht i U).honest),(fun i k U=>(hv i k U).honest),?_⟩,ht,hv⟩
    intro i z U t he x hx; unfold circular filterHard at he; dsimp only at he; by_contra hz; rw [part,solo] at he; exact he (by rw [not_not.mp (mt (fun hw=> h.stalk i z U t hw x hx) hz),not_not.mp (mt (fun hw=> h.stalk i z U (spin v t) hw x hx) hz),mul_zero,add_zero,mul_zero])
-- Transpose Part.Weight ∀ through `.circular` without cost. Central esp for repeated budget.Pole
variable (Y₀:Spring ℝ A) (hA:∀ i:V, Set.MapsTo (fun t:E i=> Complex.I • t) (A i) (A i))
include hA
local notation "↓t"=> readBack A
private def wallet (t:Wallet A):Wallet A:= Function.update t v ⟨Complex.I • (t v).val,hA v (t v).prop⟩
lemma ease (x:Wallet A): ∃ u,readBack A u= spin v (readBack A x):= by
   refine ⟨wallet v hA x,?_⟩; unfold wallet; rw [atCoord]; rfl -- rfl? use atCoord
local notation "TC"=> readH L (readBack A)
-- NONE constants grow. ∀w restore envelope also.S.H.Scope for multiple future reweights
variable {b k a:ℝ}{w:V→ℝ}
omit hA [∀ i, Module ℂ (E i)] [∀ i, AddCommGroup (E i)] [DecidableEq V] in
private lemma normedPower : ‖(2:ℂ)⁻¹‖=(1:ℝ)/2:= by norm_num -- norm_ofNat etc
lemma priced (h:(TC).Pays w a b k) : (readH C (readBack A)).Pays w a b k:=by
    obtain ⟨f,hf,he,hF⟩:= h.budget.budget
    obtain ⟨g,hg,hG⟩:= h.wages.wages
    refine ⟨⟨ f,hf,fun i t u hu=> ?_,hF⟩,⟨g,fun i t U=>?_,hG⟩⟩
    · change P.p.supBounds u (L.E.ground i) (value v L _ i) (f i); let x:= readBack A t; obtain ⟨y,hv⟩:= ease v hA t
      unfold value; rw [← hv]; let v':= meter v (L.E.mode i).val
      have ht: P.p.supBounds u (L.E.ground i) (L.E.nominal x i) (f i):= he i t u hu; have hx: P.p.supBounds u (L.E.ground i) (v' • L.E.nominal (readBack A y) i) (f i):=by
         have h₁:P.p.supBounds u _ (L.E.nominal (readBack A y) i) (f i):=he i y u hu; rw [show f i=‖v'‖* f i from by rw [show ‖v'‖=1 from itsNorm v,one_mul]]; exact bound_smul _ h₁
      have hX := bound_smul (2:ℂ)⁻¹ (bound_add (L.E.legal x i) (regular_smul v' (L.E.legal _ i)) ht hx); rw [normedPower, show (1:ℝ)/2*(f i+f i)=f i from (by ring)] at hX; exact hX
    intro j; change ‖(m (fun t=>L.K.hard t i U) (readBack A t)).part j‖≤ _ ∧ _; rw [part]; let x:= readBack A t; let u:= (g i).part j; obtain ⟨y,hv⟩:= ease v hA t; refine ⟨?_,(hg i t U j).2⟩
    unfold solo; dsimp only; rw [← hv,norm_mul,normedPower]; apply le_trans (mul_le_mul_of_nonneg_left (norm_add_le ..) (by norm_num))
    rw [norm_mul,itsNorm,one_mul]; change 1 / (2:ℝ)* (‖(L.K.hard x i U).part j‖+‖(L.K.hard (readBack A y) i U).part j‖) ≤ u.re; exact (mul_le_mul_of_nonneg_left (add_le_add (hg i t U j).1 (hg i y U j).1) (by norm_num)).trans (le_of_eq (by ring))
-- Publish & exact upholding with wallets. Use `.prospects` not norm junk for ALL t.acts. Carrier positive separate.
omit hA
open Fusion.Attached
structure Prospects (L:Gallery (Full (E:=E)) ι o P R):Prop where
    lights t U : Summable (fun i=> L.E.frame i t U)
    curtains t U : Summable (packet P.activities P.p (L.K.hard t) U)
variable [Fintype V]
variable (hl:Adult X (imported K) L) (hp:(readH L (readBack A)).Pays w a b k) (ha:0≤a)(hw:∀i,0<w i)
include Y₀ hl hp ha hw
lemma prospect : Prospects L:=by
   let L':= readH L (readBack A); have he : Y₀.card L'=L:= Spring.sticks X _ Y₀ L hl; constructor
   · intro t U; rw [← he]; exact (Spring.recalls Y₀ L' hp ha hw t U).2
   intro t U; rw [← he]; exact (Spring.recallsP Y₀ L' hp ha hw t U).2
omit Y₀ hl hp ha hw [Fintype V] in
-- ambient statements on ℝ variant and ℂ variant.Both.Comm
lemma austereCert {Q:Type}[RCLike Q][NormedAlgebra Q ℂ][∀ i,Module Q (E i)]{K:∀ i,Submodule Q (E i)} (h:Adult X K L)(U:Config G c)(i:ι): Published (K:=Q) E (fun t=> L.E.frame i t U):= by
    unfold Lamps.frame Lamps.light; split; exact letterSolo _ (h.regular i U).full
    next=>by_cases hx:Healthy P.p.threshold (L.E.ground i) U; · simp_rw [masked_eq _ _ _ _ hx]; exact letterSolo _ (h.regular i U).full
          simp_rw [masked_ne _ _ _ _ hx,Poly.send_zero]; exact Published.zero
omit Y₀ hl hp ha hw [Fintype V] in
lemma packet_pub {Q:Type}[RCLike Q][NormedAlgebra Q ℂ][∀ i,Module Q (E i)]{K:∀ i,Submodule Q (E i)} (h:Adult X K L)(U:Config G c)(i:Finset ℕ): Published (K:=Q) E (fun t=> packet P.activities P.p (L.K.hard t) U i):=by
   unfold packet; split
   next=> exact Published.prod i _ fun i _ v=> (h.hard i v U).full
   next=> exact Published.zero
omit Y₀ hl hp ha hw
lemma lithos {Q:Type}[RCLike Q][NormedAlgebra Q ℂ][∀ i,Module Q (E i)]{K:∀ i,Submodule Q (E i)} (h:Adult X K L)(hL:Prospects L)(U:Config G c): Published (K:=Q) E (fun t=> L.E.log t U)∧ Published (K:=Q) E (fun t=> L.gas t U) := ⟨Published.assembly _ (fun i=> austereCert L h U i) (fun t=> hL.lights t U),Published.assembly _ (fun i=>packet_pub L h U i) (fun t=> hL.curtains t U)⟩
lemma probates {Q:Type}[RCLike Q][NormedAlgebra Q ℂ][∀ i,Module Q (E i)]{K:∀ i,Submodule Q (E i)} (h:Adult X K L)(hL:Prospects L)(U:Config G c): Published (K:=Q) E (fun t=> L.density t U):= by let hh:= lithos L h hL U; exact Published.smul («r»:= (Real.exp _ :ℝ)) ((Published.pass hh.1).product hh.2)
private lemma flash (t:Y)(U:Config G c)(i:ι): (C).E.frame i t U=m (fun t=> L.E.frame i t U) t:=by
    ext j; rw [part]; unfold Lamps.frame; simp_rw [Poly.part_send]; rw [show (C).E.mode i=L.E.mode i from rfl]; split; next h=> subst j; exact spiral v L ..
    next=>exact (congr_fun (soloZero ..) t).symm
private lemma stage (t:Y)(U:Config G c)(h:Adult X (imported K) L)(x:Finset ℕ): packet P.activities P.p ((C).K.hard t) U x=m (fun t=> packet P.activities P.p (L.K.hard t) U x) t:=by
    unfold packet; split; next=> exact (mean_bind v t x (fun i t=> L.K.hard t i U) (fun i _ j=> (h.hard i j U).full)).symm
    next=> exact (mean_nil v t).symm
lemma through (t:Y)(U:Config G c)(h:Adult X (imported K) L)(hL: Prospects L):
    (C).density t U= mean R v (fun t=>L.density t U) t:=by
    have hp : (C).E.log t U=m (fun t=> L.E.log t U) t:=by
       unfold Lamps.log; simp_rw [flash]; exact (mean_apply v (fun i t=> L.E.frame i t U) (fun t=> hL.lights t U) t).tsum_eq
    have hk : (C).gas t U=m (fun t=> L.gas t U) t:=by
       unfold Gallery.gas; simp_rw [fun i=>stage v L t U h i]; exact (mean_apply v _ (fun t=> hL.curtains t U) t).tsum_eq
    obtain ⟨hv,hG⟩:= lithos L h hL U; unfold Gallery.density; rw [hp,hk,mean_const,mean_mul v t (Published.pass hv) hG,mean_pass v t hv]
end YM.QuadraticLocal.Affinity.Smalt
