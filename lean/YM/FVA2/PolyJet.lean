import YM.FVA2.Forge
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
/-!
# Coordinate polynomial in the scale parameter

Use Ready. On real carrier operations. Enough to derive actual differential
 assert of *formal* flow (not finite-coupling). Throughout using Word, not
 logs as Laurent arrays—need eta independent. Opens ∆Diag lower.A.N.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.FVA2.Legacy
open Function Filter Set MeasureTheory Pert Pert.Position Lattice Maxwell Maxwell.Free Pert.RawLabels PositionX PositionX.Jet PositionX.Ribbon PositionX.Detector PositionX.Bend Elegant PayAll Verne Panel Strat ColorCode Ember Pic
open MS MS.Plane MS.Land MS.Landau MS.Rake MS.High MS.Menus MS.Theater MS.Logarithm MS.Tide
open PowerSeries MS.Book MS.Book.Program MS.Book.Convolve Clock
open scoped Topology ContDiff Classical
variable {I W G Z:Type} {H:Gauge}
-- closure under multilinear read with all μ Logs. types 0. Can always specialize.
section log
variable [Fintype I] {M:I→Type}[∀i,AddCommGroup (M i)][∀i,Module ℝ (M i)][ AddCommGroup Z ][Module ℝ Z]
variable {u:ℝ→ (i:I)→M i}
lemma WearPi (h:∀ j:I,Ready (fun t:ℝ=>u t j)) : Ready u:= by
   choose n hN using h; let k:= Finset.univ.sup n; have ht(i:I) : (fun t=> u t i)∈ interest k ( M i ):= widens ( Finset.le_sup (f:=n) ( Finset.mem_univ i )) ( hN i );
   convert eval_ready k u using 1; funext x i; have hv:= interpret (ht i) x; rw [show u x i= _ from hv ]; unfold evaluate; rw [Finset.sum_apply ]; rfl
-- all Pi CPS.Dep μ arbitrary. Test runs.P.Grip.
lemma rμ {x y:ℝ→ℝ}(h:Ready x)(hp:Ready y): Ready (fun i=>x i*y i):= Ready.pair ( LinearMap.mul ℝ ℝ ) h hp
omit [Fintype I] in
lemma productμ {g:I→ℝ→ℝ}(S:Finset I) (he:∀ i∈S,Ready (g i)): Ready (fun x=> ∏ i∈S,g i x):= by
    induction S using Finset.induction_on with
    | empty=> exact funext (fun x=> (show (∏ i∈(∅:Finset I),g i x)=1 from by simp)) ▸ Ready.const _ -- cast orientation?
    | insert i s hi ih=> simp_rw [Finset.prod_insert hi ]; exact rμ (he i (by simp)) (ih fun j hj=>he j (Finset.mem_insert_of_mem hj))
lemma road (h:∀ i,Ready (fun t=>u t i))(H: MultilinearMap ℝ M Z): Ready (fun t=> H (u t)):= by
    obtain ⟨n,hN⟩:= WearPi h; let f:=Logarithm.plate n; let J:=Finset.range n; let W (i:I→ℕ):Z:= H (fun j:I=> u ( ( i j ):ℝ ) j); let T:= Fintype.piFinset (fun _:I=> J);
    have ht(t:ℝ) : H (u t)= ∑ j∈T,(∏ i:I,(f (j i)).eval t) • W j := by
       conv_lhs => rw [interpret hN t, show evaluate n u t = _ from funext (fun i=>( by unfold evaluate; rw [Finset.sum_apply]; rfl : evaluate n u t i= (∑ j∈ J,(f j).eval t • u j i))) ]; -- `congr`
       rw [MultilinearMap.map_sum_finset]; exact Finset.sum_congr rfl fun j hj=> H.map_smul_univ ..
    simp_rw [ht]; exact MS.FV2Mod.latSum T (fun j _=> Ready.smul ( productμ Finset.univ (fun i _=> Ready.got _) ) ( Ready.const ( W j ) )) -- no Fintype ℕ needed product I
end log
-- generalized.jet.plus PowerP.Set.
section generic
variable {n:ℕ} [NormedAddCommGroup W][ NormedSpace ℝ W] {w:ℝ→Word W}
    {z:W}
def polynomial (u:ℝ→Word W) : Prop:=∀ i,Ready (fun t=> u t i)
lemma constants (v:Word W) : polynomial fun _=>v:= fun _=> Ready.const _
variable (hw:polynomial w)
include hw
lemma both [NormedAddCommGroup Z][ NormedSpace ℝ Z]{g:ℝ→Word Z} (h:polynomial g): polynomial fun t=> Jet.pair (w t) (g t):= by
    intro i; let f:= (LinearMap.inl ℝ W Z); let G':= (LinearMap.inr ℝ W Z); have hp:= Ready.add_point (Ready.linear ( hw i ) f) ( Ready.linear ( h i ) G' ); convert! hp using 1; funext t; simp [pair,f,G']
lemma progress [NormedAddCommGroup Z][NormedSpace ℝ Z](hP:∀s,w s 0=z) (g:W→Z)(hc:ContDiffAt ℝ ω g z): polynomial (fun s=> run g (w s)):= by
    intro i; let F(s:ℝ):= delay (w s) i; let A(t:OrderedFinpartition i):= iteratedFDeriv ℝ t.length g z; let u(s:ℝ) (t:OrderedFinpartition i) (j :Fin t.length):=( ( t.partSize j ).factorial :ℝ ) • (w s ( t.partSize j )); let φ(i:ℕ):=( ( i.factorial:ℝ) )⁻¹;
    have hp (s:ℝ): run g (w s) i= φ i • ∑ t:OrderedFinpartition i,A t (u s t):= by
       have hf:Act i ( F s ) ( w s ):= Act.swell _ le_rfl; change someJ ( g ∘ F s ) i=_; unfold someJ; rw [ iteratedDeriv_vcomp_eq_sum_orderedFinpartition (hf.zero.symm ▸ (hP s).symm ▸ hc) hf.nice le_top, hf.zero,hP ]; simp_rw [hf.actual _ ( OrderedFinpartition.partSize_le _ _ ) ]; rfl
    simp_rw [hp]; exact Ready.scale_p ( MS.FV2Mod.latSum Finset.univ ( fun t _=> road ( H:=( A t ).toMultilinearMap ) ( fun j:Fin t.length=> Ready.scale_p ( hw ( t.partSize j ) ) _ ) )) _ -- pattern A B.H.
lemma rename (q:ℝ→ Word ℝ)(h:polynomial q): polynomial fun v:ℝ=> ren ( q v ) ( w v ):= by
    intro i; unfold Jet.ren Jet.order; apply Ready.scale_p; refine MS.FV2Mod.latSum _ ( fun j _=> ?_ ); apply Ready.smul; exact productμ _ (fun k _=> rμ ( Ready.const _ ) ( h _ )); exact Ready.scale_p ( hw _ ) _
end generic
open Clock
lemma smooth_eval {Z:Type}[NormedAddCommGroup Z][NormedSpace ℝ Z] (v:ℝ→Z) (h:Ready v) : ContDiff ℝ ω v:= by
    obtain ⟨n,hN⟩:= h; rw [ (funext ( interpret hN )) ]; unfold evaluate; exact ContDiff.sum fun i _=> (show ContDiff ℝ ω (fun t:ℝ=>(Logarithm.plate n i).eval t) from by exact Polynomial.contDiff_aeval (𝕜:=ℝ) ( Logarithm.plate n i ) ω).smul contDiff_const
lemma inverseM {q:ℝ→ Word ℝ} (h:polynomial q)(he:∀i,Genuine (q i))(hV:∀i,q i 1=1): polynomial fun v=> inverse (q v) := by
    -- cheaper reconstitute from ren recurrence.P
    let x(y:ℝ):=symbol ( q y ); let f(y):= inverse ( q y ); let A:= Complex.ofRealCLM.toLinearMap;
    have hu (k i:ℕ): Ready (fun y=>Program.cut ( x y ) k i):= by
       induction k generalizing i with| zero=> unfold Program.cut; simp_rw [pow_zero]; exact Ready.const _| succ k ih=> unfold Program.cut; simp_rw [pow_succ,PowerSeries.coeff_mul ]; apply MS.FV2Mod.latSum; intro j _; refine Ready.pair (LinearMap.mul ℝ ℂ) (ih j.1) ?_ ; simp_rw [ x,bill_q ]; exact Ready.linear ( h _ ) A -- indentation
    intro n; induction n using Nat.strong_induction_on with| h n ih=>
       have hp : ∀ y:ℝ,( ↑(f y n):ℂ)=( (headway n:ℝ ):ℂ )- ∑ i∈ Finset.range n,Program.cut ( x y ) i n*( ( f y i :ℝ ):ℂ ):= by
           intro y; have hv:= congr_arg Complex.ofReal ( congr_fun ( headback ( he y ) ) n ); rw [renReal ( inverse ( q y ) ) ((he y).1) n, Finset.sum_range_succ,ageT (litK ( he y ).1), bill_q,hV,Complex.ofReal_one,one_pow,one_mul ] at hv; rw [← hv]; abel -- x & f not defeq simpl unless change.
       have ht : Ready (fun y:ℝ=>( ↑(f y n):ℂ )):= by simp_rw [ hp ]; exact Ready.sub ( Ready.const _ ) ( MS.FV2Mod.latSum _ (fun i hi=> Ready.pair ( LinearMap.mul ℝ ℂ ) ( hu i n ) ( Ready.linear ( ih i ( Finset.mem_range.mp hi ) ) A ) )) -- lambda sint
       exact ht.linear Complex.reCLM.toLinearMap
end YM.FVA2.Legacy
