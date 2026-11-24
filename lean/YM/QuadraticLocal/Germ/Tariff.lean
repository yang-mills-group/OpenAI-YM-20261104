import YM.QuadraticLocal.Germ.Scribe
/-!
# Parent wallets vs whole letters

Supply algebraic eligibility including slot-specific test-horizon annihilators. Exact and retaining
stamps on unnormalized gas before any linear projection, not changing parameter names / proximity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal
open Lattice Wilson RG Marker
variable {T I V:Type*}{G:Gauge}{n:Side}[DecidableEq V]{R:Census V}{a: V→Site n} {P:BudgetPoint}
lemma Hard.ext {K': ℕ→ForcedAddress G n}{d:Ovens.Code G n} {Z E:Hard T P K' d a R} (h: Z.hard=E.hard) : Z=E:=by cases Z; cases E; cases h; rfl
lemma Lamps.ext {Z E:Lamps T I G P a R} (h: Z.mode=E.mode)(hp: Z.address=E.address)(hk:Z.nominal=E.nominal)(hx:Z.clear=E.clear): Z=E:=by
   cases Z; cases E; cases h; cases hp; cases hx; cases hk; rfl
end YM.QuadraticLocal
namespace YM.QuadraticLocal.Affinity
open Function Filter Finset Lattice Wilson RG Marker MeasureTheory Push Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {I V:Type}{R0:Type*}[DecidableEq V]{R:Census V}{G:Gauge}{c:Side}
variable {E: V→Type*} [∀ i, AddCommGroup (E i)]
variable {Q:Type} [RCLike Q] [NormedAlgebra Q ℂ][∀ i,Module Q (E i)]
variable {p:BudgetPoint}{P:Rep G c}{o:V→Site c}{α β γ κ r:ℝ}{B:ℕ}{w:V→ℝ}
variable (X:V→Support c) (A:∀ i,Set (E i))(K:∀ i,Submodule Q (E i))
local notation "W"=> Wallet A
local notation "T"=> Full (E:=E)
structure Adult (L:Gallery (∀ i,E i) I o P R) :Prop where
    house i v : v∈ (L.E.mode i).val→ X v⊆L.E.ground i
    regular i U : Eligible K (L.E.mode i).val fun t=> L.E.nominal t i U
    hard (i:ℕ)(q:R.Mode)(U:Config G c): Eligible K q.val fun t=> (L.K.hard t i U).part q
    stalk i q U t : (L.K.hard t i U).part q≠0→ ∀ v∈q.val,X v⊆ (P.activities.forced i).support
lemma Adult.collared {L:Gallery (∀ i,E i) I o P R}(h:Adult X K L) : Collared X A K P (readH L (readBack A)):= ⟨⟨h.house,fun i U=> (h.regular i U).restrict A⟩, ⟨fun i U=> ⟨fun q=> ⟨(h.hard i q U).restrict A,fun t=>h.stalk i q U (readBack A t)⟩⟩⟩ ⟩
section Spring
open Next.Foundations ModeWeight
variable (Y:Spring Q A)
namespace Spring
variable {A}
def booklet (x:∀ i,E i)(i:V):= (algebraMap Q ℂ) (Y.rate i (x i))
variable (L:Gallery (Wallet A) I o P R) {h:ℝ}
private def cursor (L:Lamps (Wallet A) I G p o R)(t:∀ i,E i)(i:I):= (algebraMap Q ℂ (Y.heft (L.mode i).val t)) • L.nominal (Y.profile t) i

def basis (L:Lamps (Wallet A) I G p o R): Lamps (∀ i,E i) I G p o R:= { L with
    nominal:= cursor Y L
    legal x i:= Next.Foundations.regular_smul _ (L.legal _ _)
    pure t i U h:= congr_arg ((algebraMap Q ℂ (Y.heft (L.mode i).val t)) • · ) (L.pure _ _ _ h) }
lemma basisIssue (L:Lamps (Wallet A) I G p o R)(t:∀ i,E i)(U:Config G c)(i:I): (Y.basis L).nominal t i U= Y.issue (L.mode i).val (fun a=> L.nominal a i U) t:=Eq.symm (Algebra.smul_def ..)
def program (x :∀ i,E i):= turn R (Y.booklet x)
local notation "ψ"=> program (R:=R) Y
lemma part (t:∀ i,E i) (q:R.Mode)(X:Poly R): (ψ t X).part q= Y.heft q.val t • X.part q:=by rw [program,ModeWeight.scale, Algebra.smul_def,heft,map_prod]; rfl
variable {H':ℕ→ForcedAddress G c}{F': Ovens.Code G c}
def track (F:Hard (Wallet A) p H' F' o R): Hard (∀ i,E i) p H' F' o R where
    hard t i U:= Y.program t (F.hard (Y.profile t) i U)
    locality t i:=by
       let X':=F.locality (Y.profile t) i
       refine ⟨?_, (ψ t|>.continuous.measurable).comp X'.borel, ?_, ?_⟩
       · intro v U; exact congr_arg (ψ t) (X'.gauge v U)
       · intro a b hx ht; exact congr_arg (ψ t) (X'.reads a b hx ht)
       intro U j hj; rw [part] at hj; exact X'.carry U j (fun hh=> hj (by rw [hh,smul_zero]))
    charged t i U h:= F.charged _ _ _ (fun hv=> h (by rw [hv,map_zero]))
    quiet t i U:= by rw [part, F.quiet,heft,Census.quiet,Finset.prod_empty,one_smul]
def card : Gallery T I o P R:= ⟨Y.basis L.E,Y.track L.K⟩
local notation "C"=> Y.card L
lemma forceIO (U:Config G c)(i:ℕ)(q:R.Mode)(t):((C).K.hard t i U).part q= Y.issue q.val (fun t=> (L.K.hard t i U).part q) t:= Y.part t q _
lemma employment (h:Collared X A K P L): Adult X K C := by
   refine ⟨h.lamps.house,fun i U=>?_,fun i q U=> ?_, fun i q U t he=>?_⟩
   · change Eligible K _ (fun t => (Y.basis L.E).nominal t i U); simp_rw [basisIssue]; exact Y.extend (h.lamps.adv i U)
   · simp_rw [forceIO]; exact Y.extend ((h.hard.lesson i U).each q).advice
   rw [forceIO,issue] at he; exact ((h.hard.lesson i U).each q).announces _ (fun hz=> he (by rw [hz,smul_zero]))
@[simp] lemma reverts : readH C (readBack A)= L:=by
   obtain ⟨a,b⟩:= L; unfold readH card; apply congr_arg₂ Gallery.mk
   · have h(x:Wallet A)(i:I)(U:Config G c): (Y.basis a).nominal (readBack A x) i U= a.nominal x i U:=(basisIssue Y a _ _ _).trans (by rw [Y.stay]);
     refine Lamps.ext rfl rfl (funext fun x=> funext fun i=> funext fun U=> h x i U) rfl
   · suffices h:(Y.track b).hard ∘ readBack A=b.hard by exact Hard.ext h -- no ext!
     funext x i U; ext q; exact (Y.forceIO (Gallery.mk a b) U i q (readBack A x)).trans (by rw [Y.stay]) -- order arguments
lemma sticks (L:Gallery (∀ i,E i) I o P R)(h: Adult X K L): Y.card (readH L (readBack A))=L:=by
   obtain ⟨a,b⟩:=L; unfold card; apply congr_arg₂ Gallery.mk
   · suffices h : (Y.basis (a.pullback (readBack A))).nominal = a.nominal by exact Lamps.ext rfl rfl h rfl
     funext x i U; exact (Y.basisIssue (a.pullback (readBack A)) x U i).trans (congr_fun (Y.determines (h.regular i U)) x)
   suffices hp:(Y.track (b.pullback (readBack A))).hard=b.hard by exact Hard.ext hp
   funext t i U; ext q; exact (Y.forceIO (L:=readH (Gallery.mk a b) (readBack A)) U i q t).trans (congr_fun (Y.determines (h.hard i q U)) t)

open Fusion Fusion.Attached
-- summability extension at every finite volume. No polynomial-uniform comparison cost by this statement.
lemma placid (x:Π i,E i)(U:Config G c)(s:Finset ℕ): packet P.activities P.p ((C).K.hard x) U s= ψ x (packet P.activities P.p (L.K.hard (Y.profile x)) U s) :=by unfold packet; split; exact (ModeWeight.mult _ _ _ _).symm; rw [map_zero]
lemma lit (x:Π i,E i)(U:Config G c)(i:I): (C).E.frame i x U= ψ x (L.E.frame i (Y.profile x) U):=by
   have ht : (C).E.light x i U = Y.heft (L.E.mode i).val x • L.E.light (Y.profile x) i U:=by
      unfold Lamps.light; rw [show (C).E.clear i=L.E.clear i from rfl,show (C).E.ground i=L.E.ground i from rfl]; split
      · exact Y.basisIssue L.E x U i
      next=> by_cases he: Healthy P.p.threshold (L.E.ground i) U; · rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ he]; exact Y.basisIssue L.E x U i
             rw [masked_ne _ _ _ _ he,masked_ne _ _ _ _ he,smul_zero]
   unfold Lamps.frame program; rw [send,ht,Algebra.smul_def,heft,map_prod]; rfl
variable (hs:L.Pays w α β γ)(hα:0≤α)(hw:∀ i,0<w i)(u:Π i,E i)(U:Config G c)
include hs hα hw
lemma recalls : (C).E.log u U= ψ u (L.E.log (Y.profile u) U) ∧ Summable (fun i=> (C).E.frame i u U):= by
   simp_rw [Lamps.log,Y.lit]; have hs:=(hs.budget.sums hα hw (Y.profile u) U); exact ⟨((ψ u).map_tsum hs).symm, ((hs.hasSum.mapL (ψ u))).summable ⟩
variable [Fintype V]
lemma recallsP : (C).gas u U= ψ u (L.gas (Y.profile u) U) ∧ Summable (packet P.activities P.p ((C).K.hard u) U):=by
    have H : HasSum (packet P.activities P.p ((C).K.hard u) U) (ψ u (L.gas (Y.profile u) U)) := HasSum.congr_fun ((Hard.packet_summing _ hs.wages hα hw (Y.profile u) U).hasSum.mapL (ψ u)) (placid Y L u U)
    exact ⟨H.tsum_eq,H.summable⟩
lemma tariff : (C).density u U= ψ u (L.density (Y.profile u) U):= by
   rw [Gallery.density,Gallery.density,map_smul,(recalls Y L hs hα hw u U).1,(recallsP Y L hs hα hw u U).1, program, ModeWeight.rum,ModeWeight.pass]
end Spring
end Spring
section Apart
lemma readThrough [Fintype V] {α α':Type*} (X':Gallery α I o P R) (g:α'→α)(t:α') : (readH X' g).density t=X'.density (g t):=rfl
end Apart
end YM.QuadraticLocal.Affinity
