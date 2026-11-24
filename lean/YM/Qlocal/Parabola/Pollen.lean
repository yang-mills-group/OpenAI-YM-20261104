import YM.Qlocal.Parabola.StoryK
/-!
 Repaint ONLY marked side (each correction converted to monomial additions,
 at the old/new union flag). No small unmarked part needed (old E kept or
 use M1 first). Ratio expressed directly at Occupied.Risk.Probe. Not silently expecting
 integer incidence cap.Pic.Ui. Keep original tests and Shot.Choice vertex sets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Parabola
open Function RG Lattice Wilson Pert.Attach MeasureTheory Filter Progress.DirectedRecipe Finset
open Marker RG03.Gather Bank Push.AbsoluteSums
open scoped Topology ContDiff BigOperators Classical
open Publishing
variable {G:Gauge}{n:Side}{w t v c d b δ κ:ℝ}{k:ℕ}{V Ω ι:Type}[DecidableEq V]{R:Census V}
    {A:Activities G n} {P:BudgetPoint}{s:V→Support n}
    {L:ι→Ray R}{U:ι→Support n}{q:Ray R}
namespace Haze
variable (p:Rental q) (H:Haze U k t L q v)
variable (hw:0≤t)(he:∀ i,(U i).Nonempty)
include p H hw he
lemma summable_ledger (x:R.Mode): Summable fun i=> L i x:=by
 let v i:=Parabola.bill q (L i); have hx(i):0≤v i:=bill_nn (H.1 i) p.oneSize
 have hg: Summable v:= (Product.everyone_ne U _ hx (fun i _=>he i) H.2).2.1.of_nonneg_of_le hx (fun i=> le_mul_of_one_le_right (hx i) (Real.one_le_exp (mul_nonneg hw (by positivity : 0≤(coverNumber k (U i):ℝ)))))
 have hs(i):q x*L i x ≤ v i:= Finset.single_le_sum (f:=fun y:R.Mode=> q y * L i y) (fun j _=> mul_nonneg (p.pos _).le (H.1 i j)) (Finset.mem_univ x)
 exact (hg.mul_left (q x)⁻¹).of_nonneg_of_le (fun i=> H.1 i x) (fun i => (le_inv_mul_iff₀ (p.pos _)).mpr (hs i))
lemma summable_units {F:ι→Poly R} (hf:∀ i,CoverP (L i) (F i)) (g:V→ℝ)(hg:∀ i,0<g i) : Summable fun i=>Marker.Poly.price g (F i):= by
 let p' i x:= Poly.toll g x*L i x; have he:Summable fun i=>∑ x:R.Mode,p' i x:= summable_sum fun x _=> (H.summable_ledger p hw (by assumption) x).mul_left _ -- syntax
 exact he.of_nonneg_of_le (fun i=> Poly.nonnegative hg _) (fun i=> Finset.sum_le_sum (fun x _=> mul_le_mul_of_nonneg_left (hf i x) (Poly.worth hg _).le))
end Haze

abbrev Policy (G:Gauge)(R:Census V)(n:Lattice.Side) := ℕ→ Config G n→Poly R
variable {S: Corrections G n}
-- generic repaint.ALL old predicates retained; stamp includes integer alignment and masks. No finite orientation independent tests aggregated with volume slack.
structure Authority (P:BudgetPoint)(A:Activities G n)(s:V→Support n)(K:Policy G R n):Prop where
   align : ∀ i,Articles (A.forced i).support (K i) s P.threshold
   beacon i U : K i U ≠ 0 → (A.forced i).eligible P.threshold U
   quiet i U : (K i U).part R.quiet=(A.K i U:ℂ)
variable [Fintype V]
structure Changes (P:BudgetPoint)(X:Corrections G n)(Y Y':Config G n→ Poly R) (I : ℕ→ Config G n→ Poly R) (s:V→Support n):Prop where
   reads :∀ i, Articles (X.region i) (I i) s P.threshold
   silent i U : (I i U).part R.quiet=0
   expires i U (h:Healthy P.threshold (X.region i) U): I i U=0
   impact i U : Poly.pass (I i U)=1+ I i U
   exponent U : Y U=Y' U +∑' i,I i U
   noun U: (Y' U).part R.quiet=0
-- explicitly assembler. true.Re.Context.Ve.
variable (C: Bank A P.threshold)
    {Y Y': Ω→ Config G n→Poly R}{I K: Ω→ Policy G R n}
    {L J: ℕ→ Ray R}
variable (p:Rental q)
variable (hK: Haze (fun i=>(A.forced i).support) P.B (t+δ) L q v)
  (hI:Haze S.region P.B (t+δ) J q b)
  (hS:A.ForcedFamily P)(hx:∀ x:Ω,Authority P A s (K x))(ht:∀ x,Changes P S (Y x) (Y' x) (I x) s)
  (hL:∀ x i U,CoverP (L i) (K x i U))(hJ:∀ x i U,CoverP (J i) (I x i U))
set_option quotPrecheck false
local notation "Y0"=> (fun x=> C.store S P (K x) (I x))
def session (P:BudgetPoint) (A:Activities G n)(K:Policy G R n) (Y:Config G n→Poly R)(U:Config G n):= Poly.pass (Y U) * ∑' t, Merge.Photo.fronts A (fun i=> K i U) U P t
include C hK hI hx ht hL hJ p
lemma record_cost (hw:0 ≤ t+δ)(h:∀ i,(S.region i).Nonempty) (x:Ω) : session P A (K x) (Y x)= session P A (Y0 x) (Y' x):= by
 ext1 U; unfold session; let w:=fun _:V=>(1:ℝ); let F₀:=fun i:ℕ=> I x i U; have hw'(i:V):0<w i:=zero_lt_one; have hp:Summable fun i=> Poly.price w (F₀ i):= hI.summable_units p hw h (fun i=> hJ x i U) w hw'
 have hs: Summable F₀:= (Poly.budgeted hw' hp (fun i=>le_rfl)).1; let v':= Y' x U; let K':= fun x:R.Mode=>x; let H(U:Config G n):= ∑' i,I x i U; have hT: (H U).part R.quiet=0:=by unfold H; rw [Poly.share hs]; exact Eq.trans (tsum_congr (ht x|>.silent · U)) tsum_zero -- signature
 have hT': H U=∑' i,I x i U:=rfl; have hμ:Summable fun i=>Poly.price w (K x i U):= hK.summable_units p hw (fun i=> (A.forced i).inventory_ne.mono (A.forced i).inventory_sup) (fun i=> hL x i U) w hw'; change Poly.pass _ * poem A P (K x) U = Poly.pass _ * poem A P (C.store S P (K x) (I x)) U; rw [C.stored S P (K x) (I x) U hw' (hx x).beacon (ht x).expires hμ hp,(ht x).exponent U,Extra.Trajectories.pass_add (ht x|>.noun U) hT]; let d:= RG03.liftExp_hasProd (fun _:ℕ=>(0:ℝ)) F₀ (fun i=> (ht x).silent i U) summable_zero hs; have hr: ∏' i,(1+I x i U) = Poly.pass (∑' i,F₀ i):= by rw [tprod_congr (g:=fun i=> RG03.liftExp 0 (F₀ i)) ?_, d.tprod_eq]; simp only [tsum_zero,RG03.liftExp,Real.exp_zero,Complex.ofReal_one,one_smul]; intro i; simp_rw [RG03.liftExp,Real.exp_zero,Complex.ofReal_one,one_smul]; exact ((ht x).impact i U).symm
 rw [hr]; unfold F₀; ring -- Ext argument.W.Resources stanza.
include hS
lemma preserved (he:∀ i,(S.region i).Nonempty) (hv:StellarTree.sites P.B * (κ*v+b) ≤ δ)(hw:0≤t)(hκ:1≤κ)(hd:0≤δ) :
    (∀ x,session P A (K x) (Y x) = session P A (C.store S P (K x) (I x)) (Y' x) ∧ Authority P A s (C.store S P (K x) (I x))) ∧ Haze (fun i=>(A.forced i).support) P.B t (L + Parabola.dawn C S L J) q (v+κ⁻¹*(Real.exp (κ*v+b)-1)) ∧ ∀ (x:Ω)(i:ℕ)(U:Config G n),CoverP (L i + Parabola.dawn C S L J i) ((C.store S P (K x) (I x)) i U):= by
 refine ⟨fun x=> ⟨?_,?_⟩, broadcast _ _ _ I K p hK hI hL hJ hκ hv hw hd⟩ -- signature?
 · exact record_cost C p hK hI hx ht hL hJ (add_nonneg hw hd) he x
 let H(x:Ω)(i:ℕ):= equipped (fun x=>(hx x).align) (fun x=>(ht x).reads) hS (fun x=>(hx x).quiet) (fun x=>(hx x).beacon) (fun x=>(ht x).silent) C x i
 exact ⟨fun i=>(H x i).1,fun i U=>(H x i).2 U|>.2,fun i U=>(H x i).2 U|>.1⟩
end YM.Qlocal.Parabola
