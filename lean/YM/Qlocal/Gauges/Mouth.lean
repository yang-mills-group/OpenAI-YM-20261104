import YM.Qlocal.Reckoner.Tatami
/-!
# ROOT work at entrance of ACTUAL Step. Use both Peak, and separate analyt annotations at stencil sites.
 Re-expressing gas labels from residual.Preserves normalization. Mode algebra
 projected after reconciled illumination. -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Gauges
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open Next.Foundations PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators YM.Qlocal.Payload
open Merge Switch UniformPays Publishing Emissions Payload MergeProof Menu Accent Lotus Reckoner Parabola
open RGComparison01 RGComparison01.Pledge
variable {Ω ι J V I : Type} [DecidableEq V] {R:Census V} {G:Gauge}{n c:Side}{P: RG.Rep G n}
    {o:V→Site n}{s:V→Support n}{Zμ:ℝ}{S:StepData c n}
    {u:R.Mode→ℝ}{y:J→ℝ}
    {a b v t δ C A B θ ρ:ℝ}
    {Y:Taste Ω o P R}{dcl:Set (ℕ ×ℕ)}
    {hw:RetainsDeclared dcl Y s}{hv:Peak P o Y u P.p.supportExponent A B} {x₀:Ω}(V': Payload.Fabric hw hv x₀)
namespace Binder
-- adaptor uses even shutter mask vs Template.Clock outside ordinary log, orientation based.True direct valuation. Connector from pTag per output wishes.
variable (O: J→ Hat R P)(U:Config G n)
structure Alone : Prop where
   eyes (i j:J)(p:ℕ) : WKey (O i)=Wing.logKey p → WKey (O j)=Wing.logKey p → (O i).s=(O j).s
variable [Fintype J][Fintype V]
include U
lemma Alone.jets {O:J→ Hat R P}(hp:Alone O): Menu.jets O U=Poly.pass (∑ i,odour (O i) U):=by
 rw [← perfumes]; let f(i:ℕ):= rush O (.logKey i) U; let S:= logDeck O; have h: ∀ i:S,∃ θ:R.Mode, θ.val.Nonempty ∧∀ j:J,WKey (O j)=Wing.logKey i.val →(O j).s=θ:= by
   intro i; obtain ⟨j,hj⟩:=(Menu.cams O i.val).1 i.prop; exact ⟨(O j).s, (O j).shiny,fun i' hi=> hp.eyes _ _ i.val hi hj⟩
 choose v hv ht using h; let g(i:S):=(f i.val).part (v i); have hg(i:S):Poly.send (v i) (g i)= f i.val := by
    ext a; rw [Poly.part_send]; by_cases h:a=v i; rw [h,if_pos rfl]
    rw [if_neg h]; unfold f rush; rw [Poly.part_sum]; symm; refine sum_eq_zero fun j _=>?_ ; split; next hh=> rw [varnish,Poly.part_send,if_neg (mt (fun he=> he.trans (ht _ _ hh)) h)]
    next=>rfl
 unfold Menu.jets roll; rw [← prod_coe_sort S,← sum_coe_sort S]; change (∏ i:S, (1+f i.val))=_; rw [show (∑ i:S,rush O (Wing.logKey i.val) U)=∑ i:S,f i.val from rfl]; simp_rw [← hg, Extra.Trajectories.pass_sum univ v (fun i _=>hv i) g]
-- reweight.Menu any pose scales.Learn.Ar.Low.Tick
lemma native_book (S:StepData c n) (g:J→ℝ)(w:J→ℂ)(h:∀ i,(↑(g i):ℂ)*w i=(O i).charge)(hP:P.Lawful θ Zμ t b C):
     Photo.given (S:=S) (fun i=>(O i).M) g R (fun i=>Poly.send (O i).s (w i)) U=(Real.exp (P.exponent U):ℂ) • (Menu.jets O U*field (fun i=>bar P.activities R U i+board O i U) (RG.flags P.p.threshold U)):=by
 rw [← Menu.passIn O S hP (fun _=>zero_lt_one)]; refine Provisional.common _ _ _ _ _ _ ?_ _; intro i; rw [Menu.purchase _ (fun _=>zero_lt_one),Menu.sent,h]; rfl
section entry
local notation "DK"=> deck R s
variable (Z:HasSlots P.p P.activities) (F:J→ℕ)(x:Ω) (hn:P.Lawful θ v t b C)
local notation "G₀"=> profileH Z V' x
local notation "Lℓ"=> (Sum.elim G₀ O)
include hw hv Z hn S
private theorem true_cost (he:∀ i,0<u i):
    let T':=G₀; ((Y.leaf x).contents).density U=(Real.exp (P.exponent U):ℂ) • (Menu.jets T' U *field (fun i=> bar P.activities R U i+board T' i U) (RG.flags P.p.threshold U)):= Eq.trans (Payload.borrows rfl he Z V' x U hn S (fun _=>1) (fun _=>zero_lt_one)).symm (Menu.passIn _ S hn (fun _ => zero_lt_one) _) -- S not included
variable (hp:∀ i, WKey (O i) =.logKey (F i)) (he:Alone (Sum.elim (profileH Z V' x) O))
variable {z:Payload.deck R s ⊕ J→ℝ}{f:Payload.deck R s⊕ J→ℂ}
include hp he S
lemma birth (h:∀ i,(↑(z i):ℂ)*f i=(Lℓ i).charge) (hc:∀ i,0<u i): Photo.given (S:=S) (fun i=>(Sum.elim (profileH Z V' x) O i).M) z R (fun i=>Poly.send (Lℓ i).s (f i)) U= Poly.pass (∑ i,odour (O i) U) * (Y.leaf x).contents.density U:=by
 let T' := G₀; have hg : Alone T':= ⟨fun i j k hi hj=> he.eyes (Sum.inl i) (Sum.inl j) _ hi hj⟩
 have hx: (∑ i:DK⊕ J,odour (Lℓ i) U)= (∑ i:DK,odour (T' i) U)+(∑ i:J,odour (O i) U):=Fintype.sum_sum_type _
 have hQ(k):board Lℓ k U=board T' k U:=by rw [patron,patron, Fintype.sum_sum_type,sum_eq_zero (s:=@Finset.univ J _) (f:=fun j=>fragrance (Lℓ (Sum.inr j)) U k),add_zero];rfl; intro i _; unfold fragrance MergeProof.entry; simp only [Sum.elim_inr,show (O i).M.turn= .logKey _ from hp i]; simp
 let Yz (i:DK ⊕ J):= Lℓ i; rw [native_book (Lℓ) U S _ f h hn,true_cost (S:=S) V' U Z _ hn hc, Alone.jets U he,Alone.jets U hg]; simp_rw [hx,hQ]; rw [Extra.Trajectories.pass_add,mul_smul_comm]; rotate_left
 · rw [← perfumes]; unfold roll; exact (Poly.part_sum ..).trans (sum_eq_zero (fun i _=> Menu.still ..))
 · rw [← perfumes]; unfold roll; exact (Poly.part_sum ..).trans (sum_eq_zero (fun i _=>Menu.still ..))
 · rw [mul_comm (Poly.pass (∑ i:DK, odour (T' i) U)),mul_assoc]
end entry
end Binder
end YM.Qlocal.Gauges
