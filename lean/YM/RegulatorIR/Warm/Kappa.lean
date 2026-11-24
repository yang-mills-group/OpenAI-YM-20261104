import YM.RegulatorIR.Warm.Rounder
import YM.RegulatorIR.Oracle.Life

/-!
# Patch-preferred primitive templates. All connector prices depend here
on one chosen patch BEFORE paying steps. Scalar omitted exactly. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Warm
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
variable {G:Gauge}{X Y I J:Type}{s m p e j r:ℕ}{c f:Side}{l P:ℝ}
section Summ
variable {A:Deck P X Y}{B:Parade I J}{T:I→Packet X p} [Fintype J]
-- At least one leg allows only finitely many contributing roots.
lemma finite_roots (h: Rot A B T)(ht:∀ i,Bounded (T i))(i:Fin p)(x:Tuple X p) : (Function.support (fun v=>T v x)).Finite:=by
 let f(I:I):= B.rolls.symm I; let v(i:I):= (A.wind (f i).1).symm ∘ x
 let L:= fun z:I=>((f z).2,v z)
 have hv (i:I) : A.wind (f i).1 ∘ v i=x:= by ext j; simp [v]
 have hm : Injective L:=by
    intro i' j hh; have he:(f i').2=(f j).2:= congr_arg Prod.fst hh; apply B.rolls.symm.injective; refine Prod.ext ?_ he
    let u:=v j;have hp:= congr_fun (hv j) i; change A.wind (f j).1 (u i) = _ at hp
    apply (A.edges (u i) (x i) (by rw [← hp,A.projected])).unique _ hp
    unfold u;rw [← show v i'=v j from congr_arg Prod.snd hh]; exact congr_fun (hv i') _
 let R:= ⋃ j:J, ({j}: Set J) ×ˢ Function.support (T (B.bare j)); have hR:R.Finite:= Set.finite_iUnion fun j=> (Set.finite_singleton j).prod (ht _)
 refine (hR.preimage hm.injOn).subset ?_;intro a (ha:T a x ≠0)
 have hp(f): (A).polish f≠0:= left_ne_zero_of_mul (show (A).polish (f:Tuple X p)* (A).polish f≠ (0:ℝ) by rw [Deck.polish_sq]; exact one_ne_zero)
 apply Set.mem_iUnion_of_mem (i:=(f a).2); refine ⟨Set.mem_singleton _, ?_⟩
 intro h'; have H:= h (f a).1 (B.bare (f a).2) (v a); rw [hv, show B.rips _ _=a from (B.puts ..).symm.trans (B.rolls.apply_symm_apply _)] at H
 exact mul_ne_zero ha (hp x) (H.trans (by unfold dyed; rw [show T _ _=0 from h',zero_mul]))
end Summ
section Scaffold
variable (K:KernelChoices) (F:Patch)
private lemma ht : Even (4:Side).val:=even_two_mul 2
private lemma hf (F:Patch): Even (cabins F).val:= ht.mul_right _
private def power (F:Patch):ℝ:=4*F.L.val
private lemma phaseA (F:Patch): (1:ℝ)*(cabins F).val=power F:=by unfold cabins power;push_cast; ring
private lemma phaseB (F:Patch): (F.L.val:ℝ)*(4:Side).val=power F:=by unfold power;push_cast;ring
private def anchorK (G:Gauge): Deck (power F) (KFoot G) (Book G (4*F.L) ⊕ Book G (4:Side)) := Step.combine (Carto G _ _ (hf F) (phaseA F)) (Carto G _ _ ht (phaseB F))
local notation "L"=> avenue F K 4
variable (G:Gauge)(Z:F.Branches K G)
lemma wingR : Flight (opi L Clocks.flat) (standby (S:=L) Z) (fun _=>0) (fun _=>-1) (anchorK F G) (posMarch ht):=⟨footing L Z _ _ _ _ _,boosted Z,fun _=>by decide,fun _ _=>rfl,fun _ _=>rfl,opi_zero L Z Clocks.flat⟩ -- opi_zero order
lemma wingL : Flight (carnal L (stemF F 4)) (ringQ F K G Z) (fun _=>0) (fun _=>1) (anchorK F G) (posMarch (hf F)):=⟨carnal_o _ _ _ _ _ _,(fun i=> ((rooted (G:=G) L (stemF F 4) i).some.issues (1:ℝ) 0).choose_spec),fun _=>by decide,fun _ _=>rfl,fun _ _=>rfl, fun x s=>carnal_z L (stemF F 4) G ..⟩
private def tagQ (j : ℕ) := (Tariff.native (F.L.val:ℝ) (by positivity) j).uses (anchorK F G).pos

def disksR (j i k:ℕ): ℝ≥0∞:= ∑ z:OEdge 4, quota (standby (S:=L) Z ((posMarch ht).bare z) j i) (tagQ F G k).diameter
def disksL (j i k:ℕ): ℝ≥0∞:= ∑ z:OEdge (4*F.L), quota (ringQ F K G Z ((posMarch (hf F)).bare z) j i) (tagQ F G k).diameter
-- harmless k may be any moment already paid $ν$.
lemma disk_f (j i k): disksR K F G Z j i k≠⊤ ∧ disksL K F G Z j i k≠⊤:=by
 let V:= tagQ F G k; have h(x y): V.road x y≠⊤:= ENNReal.pow_ne_top ENNReal.ofReal_ne_top
 exact ⟨ENNReal.sum_ne_top.mpr (fun z _ => Oracle.boundedC (Lab.sized ((wingR K F G Z).value _) _ _) h), ENNReal.sum_ne_top.mpr (fun z _ => Oracle.boundedC (Lab.sized ((wingL K F G Z).value _) _ _) h)⟩
private lemma wavesA {p':ℝ}(h:p'=l*F.L.val)(ht:0 < p')(j:ℕ): (Tariff.native p' ht j).uses (peak_o G l p')=tagQ F G j:=by -- p' unknown
 let r:ℝ:=F.L.val;have hp:0<r:=by unfold r; positivity
 let Q:=anchorK F G
 have hz(i): peak_o G l p' i=l • Q.pos i:=by
    cases i
    · rename_i i;exact native_shift l i
    rename_i i; rw [h]; change Geometry.seat (l*r) i.fst=l • Geometry.seat r i.fst; rw [native_shift (l*r) i,native_shift r i, smul_smul] -- smul_eq?
 have hl:0<l:= pos_of_mul_pos_left (show 0<l*r from h ▸ ht) hp.le
 have he : ∀ T U:Tariff (KFoot G),T.road=U.road→ T=U:=by intros T U h; cases T; cases U;congr
 apply he;ext1 i; ext1 k; change Tariff.amount p' j (dist (peak_o _ _ _ i) (peak_o _ _ _ k))=Tariff.amount r _ (dist (Q.pos i) (Q.pos k));rw [hz,hz,dist_smul₀, Real.norm_of_nonneg hl.le,show p'=l*r from h]; unfold Tariff.amount; rw [mul_div_mul_left _ _ hl.ne']
variable {S:Scale}{U:Branchix→ Orders (KFoot G)}
private lemma straits {T:StepData c f}(p:T.patch= F)(t:T.kernel=K)(h: Sphere T (bios T) S U): Sphere L (stemF F 4) S U:=by
 have hv:= Older.neverP (G:=G) T L p t S
 intro x;rw [show prism L (stemF F 4) S x= _ from congr_fun hv.symm x]; exact h x

def mainL (j:ℕ): Ranked (KFoot G):=many (ringQ F K G Z) j
def mainR (j:ℕ): Ranked (KFoot G):=many (standby (S:=L) Z) j
-- price all rank and β difference, no visibility dependence on n f
lemma localK (k i j:ℕ) {p':ℝ}(hL: p'=l*F.L.val)(hp':0<p') : let p:=(Tariff.native p' hp' k).uses (peak_o G l p'); localQ p (mainL K F G Z j i) (disksL K F G Z j i k) ∧ localQ p (mainR K F G Z j i) (disksR K F G Z j i k):= by
 dsimp only;rw [wavesA F G hL hp']; let A:= anchorK F G
 refine ⟨Oracle.axi_cost A (posMarch (hf F)) (tagQ F G k) _ ((wingL K F G Z).paves j i) (Oracle.capableM A (u:=k) (l:=(F.L.val:ℝ)) (by positivity)), Oracle.axi_cost A (posMarch ht) (tagQ F G k) _ ((wingR K F G Z).paves j i) (Oracle.capableM A (u:=k) (l:=(F.L.val:ℝ)) (by positivity))⟩


private lemma passSum {f:I⊕J→ℝ}{g:I→ℝ}{V:X→J→ℝ}{S:Finset X} (c:X→ℝ)(h:∀ x,f (.inr x)= ∑ p∈S,c p *V p x)(hh:∀ x,f (.inl x)=g x)(ht:Summable g)(hp:∀ i,Summable (V i)): (∑' x,f x)= (∑'x,g x)+∑ p∈S,c p* (∑' j,V p j):=by
 rw [Summable.tsum_sum]; simp_rw [hh,h]; apply congr_arg; rw [Summable.tsum_finsetSum (fun i _=>(hp i).mul_left _)];simp_rw [tsum_mul_left]
 · rw [show f ∘ Sum.inl=g from funext hh]; exact ht
 unfold Function.comp;simp_rw [h]; apply summable_sum; exact fun i _=> (hp i).mul_left _
lemma fullK {T:StepData c f}(p:T.patch=F)(t:T.kernel=K)(h:Sphere T (bios T) S U) (j:ℕ)(hj:0<j) : many U j= mainL K F G Z j+∑ i∈ Finset.antidiagonal j,biases S i.1 • mainR K F G Z (i.2+2):=by
 have hv:=straits K F G p t h
 let g:= ringQ F K G Z;let f:= standby (S:=L) Z;let N:=Finset.antidiagonal j
 have ha(x): U (.inl x)=g x:= Lab.unique (hv (.inl x)) ((wingL K F G Z).value _)
 have he(x): U (.inr x) j=∑ i∈ N,biases S i.1 • f x (i.2+2):= milk (S:=L) Z S (x:=x) (W:=U (.inr x)) (hv (.inr x)) j hj
 ext1 i; ext1 x; change (∑' u,U u j i x)= mainL _ _ _ _ j i x+(∑ i∈ N,biases S i.1 • mainR K F G Z (i.2+2)) i x
 have hz(r:ℕ): Summable (fun p=> f p r i x):=by
    by_cases he: 0 < i
    · apply summable_of_hasFiniteSupport; apply finite_roots ((wingR K F G Z).paves _ _ ) (fun v=>(boosted Z v).sized _ _) (i:=⟨0,he⟩)
    have hu:i=0:=by omega
    subst i
    simp_rw [fun p=> show f p r 0 = _ from (boosted (S:=L) Z p).no_altar (opi_zero L Z Clocks.flat p) r]; exact summable_zero
 have hh:Summable (fun p=>g p j i x):=by
    by_cases he: 0 < i
    · exact summable_of_hasFiniteSupport (finite_roots ((wingL K F G Z).paves j i) (fun i=>((wingL K F G Z).value _).sized ..) ⟨0,he⟩ x)
    have hu:i=0:=by omega
    subst i
    simp_rw [fun p=> show g p j 0 = _ from ((wingL K F G Z).value p).no_altar (fun v=> carnal_z (avenue F K 4) (stemF F 4) G p v) j]; exact summable_zero
 simp_rw [Finset.sum_apply,Pi.smul_apply]; change (∑' v, _)= (∑' q,g q j i x) + ∑ u∈ N,biases S u.1* ∑' p,f p (u.2+2) i x
 refine passSum (S:=N) _ (fun r=>?_) (fun i'=> by rw [ha i']) hh (fun i=>hz (i.2+2))
 rw [he];simp_rw [Finset.sum_apply];rfl
-- slope carrier, map qualifying fine axis.H.
lemma carriersK {T:StepData c f}(p:T.patch= F)(t:T.kernel=K)(h:Billed (finer (fringe T (X:=G.ColorIndex))))(h':Billed (Function.swap (finer (fringe T (X:=G.ColorIndex))))): mainR K F G Z 2 = peak (coil (warmP K.penalty (finer (fringe T (X:=G.ColorIndex))))):=by
 subst F; subst K; ext1 r
 change massive _= _; simp_rw [show ∀ x,standby (S:=avenue T.patch T.kernel 4) Z x 2= _ from fun x=> pivot_s _ _ Z]; by_cases he:r=2
 · subst r; simp_rw [peak_at]; exact fuel_goal _ h h'
 rw [peak_dark _ he]; simp_rw [fun z=> peak_dark (seatQ T G z) he]; ext1 x; simp [massive]
end Scaffold
end YM.RegulatorIR.Warm
