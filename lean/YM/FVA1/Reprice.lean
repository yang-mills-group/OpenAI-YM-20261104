import YM.FVA1.Fuse
import YM.Gaps1020.Local.Wear

/-! Commutation of a supported finite analytic/test menu with its re-expression on
separate occurrence-marker variables. -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA1.MenuBridge
open MeasureTheory Finset Function Filter Lattice Wilson RG RG05.Strand Extra.Trajectories
open Marker Overlay Overlay.GapsLocal Push.GridApprox.Nil MergeProof Accent Menu Merge Merge.Palette
open Push Push.AbsoluteSums PhysicalNext.Repeat GapsLocal.Full
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {T I V:Type}[Fintype I] [Fintype V][DecidableEq V]
variable {G:Gauge}{f:Side}{R:Rep G f}{Γ:Census V}
variable (q:I→Menu.Hat Γ R)(read:I→(V→T)→ℂ)
variable (σ:V→ℝ)

-- field-independent test read on each old deck entry

def lengthen (i:Mound q) (φ:V→T) :ℂ:=
  i.elim (fun i=>read i φ) fun j=>∏ i∈j.2.val.val, read i φ

def vital (φ:V→T):I→Hat Γ R:=fun i=> { q i with charge:= (q i).charge * read i φ }

def clipTest (v:V→ℝ)(i:Mound q)(φ:V→T):ℂ:= lengthen q read i φ * ((heap q i).charge / (sumFee (heap q i) v:ℂ))

omit [Fintype V] in
lemma clipLinear [AddCommGroup T] [Module ℂ T] (i:Mound q) (h:∀ i,SlotLinear (q i).s.val (read i)):
    SlotLinear (heap q i).s.val (clipTest q read σ i):=by
    let p:= heap q i; let c:= p.charge/(sumFee p σ:ℂ)
    change SlotLinear p.s.val _; rw [show clipTest q read σ i=c • lengthen q read i from funext fun φ=> mul_comm ..]
    refine SlotLinear.smul ?_ _
    unfold p; cases i with
    | inl i=> exact h i
    | inr i=>
      let F:= fun j=> hatMode q j|>.val
      have hA:(i.2.val.val:Set I).PairwiseDisjoint F:= i.snd.val.property.2.2.1
      have he:= SlotLinear.prod i.snd.val.val hA (f:=read) (fun j _=> h j)
      change SlotLinear (i.snd.val.val.biUnion F) (fun φ=> ∏ j∈ i.snd.val.val, read j φ)
      simpa only [← Finset.prod_apply] using he

omit [Fintype V] in
lemma summed_stub (i:Mound q)(X:Positions V f)(h:∀ i,∀ j∈(q i).s.val,X.stub j ⊆ (q i).M.crest):
    ∀ j∈ (heap q i).s.val,X.stub j ⊆ (heap q i).M.crest:=by
    intro j hj; cases i with
    | inl i=> exact h i _ hj
    | inr d=>
      let p:=d.snd.val
      obtain ⟨x,hx,hx'⟩:= Finset.mem_biUnion.mp hj
      have hX:=h x j hx'
      change X.stub j ⊆ (WKey (q x)).support R at hX
      rw [show WKey (q x)= .logKey d.fst.val from (mem_filter.mp (p.property.2.1 hx)).2] at hX
      exact hX

variable (hx:∀ i,0<σ i)
omit [Fintype V] in
lemma length_limit (φ:V→T)(hf:∀ i,‖read i φ‖ ≤ 1)(i:Mound q): ‖lengthen q read i φ‖ ≤ 1:=by
    cases i with
    | inl v=> exact hf v
    | inr v=>
      change ‖∏ i∈v.2.val.val,_‖≤ _; rw [norm_prod]; exact Finset.prod_le_one (fun _ _=> norm_nonneg _) (fun i _=>hf i)

include hx
omit [Fintype V] in
lemma clip_limit (φ:V→T)(hf:∀ i,‖read i φ‖ ≤1)(i:Mound q): ‖clipTest q read σ i φ‖ ≤ (Poly.toll σ (heap q i).s)⁻¹ :=by
    let c:=sumFee (heap q i) σ
    have h : Poly.toll σ (heap q i).s * ‖((heap q i).charge/(c:ℂ))‖ ≤ 1:= by convert Menu.paid (heap q i) hx; symm; exact Poly.solo ..
    rw [clipTest,norm_mul]; apply le_trans (mul_le_mul_of_nonneg_right (length_limit q read φ hf i) (norm_nonneg _)); rw [one_mul,← one_div,le_div_iff₀' (Poly.worth hx _)]
    exact h

omit hx
-- heap depends on layout only, its type and physical Leaf displayed above are unchanged
omit [Fintype V] in
lemma heap_price (φ:V→T)(i:Mound q): (heap (vital q read φ) i).charge= (heap q i).charge * lengthen q read i φ:=by
    cases i with
    | inl j=> rfl
    | inr j=> change ∏ i∈j.snd.val.val, ((q i).charge * read i φ)= _; rw [Finset.prod_mul_distrib]; rfl

include hx
omit [Fintype V] in
lemma pays_clip (φ:V→T)(i:Mound q): ((sumFee (heap q i) σ:ℝ):ℂ) * clipTest q read σ i φ=(heap (vital q read φ) i).charge:=by
    rw [heap_price,clipTest]; let a:=(heap q i).charge; by_cases h:a=0; · change _*((_)*(a/_))=a*_; rw [h]; simp
    have hz:0 < sumFee (heap q i) σ:= mul_pos (Poly.worth hx _) (norm_pos_iff.mpr h); have he':(↑(sumFee (heap q i) σ):ℂ)≠0:=by exact_mod_cast hz.ne'
    field_simp

omit hx
-- expose AnalyticMenu input as actual complete exponential before evaluation.
def offered (hdr:V→(V→T)→ℂ)(φ:V→T): Config G f→Poly Γ:= YM.GapsLocal.Full.given (vital q read φ) (fun i=> hdr i φ)

-- use given (M:Leaf) with unconstrained occurrence names. b' directly fires i
variable {c:Side}

def counts0 (S:StepData c f): Config G f → Poly (FreeCensus (Mound q)):= Photo.given (S:=S)
  (fun i=>(heap q i).M) (fun i=>sumFee (heap q i) σ) (FreeCensus (Mound q))
  (fun i=> Poly.send ((FreeCensus (Mound q)).fire i) 1)

omit [Fintype V] in
lemma counts_integrable (S:StepData c f){a b e v x:ℝ}(h:R.Lawful a b v x e): Integrable (counts0 q σ S) (prior G _):=by
    let m:=Mound q
    unfold counts0 Photo.given; refine integrable_finsetSum _ fun i _ => ?_
    exact ((((team _ i).sells h).1.integrable _).mul_const _).smul_const _

set_option quotPrecheck false
local notation "decode" φ:max => decoder (fun i=>(heap q i).s) (fun i=> clipTest q read σ i φ)

include hx
lemma counted (S:StepData c f){a b e v x:ℝ}(h:R.Lawful a b v x e) (hdr:V→(V→T)→ℂ)(φ:V→T)(U:Config G f):
    offered q read hdr φ U=Poly.pass (Mach Γ (fun i=> hdr i φ)) * (decode φ) (counts0 q σ S U):=by
    unfold offered
    rw [fragrant (vital q read φ) (fun i=> hdr i φ) S h hx]; unfold ConnectedActivityE6.Blaze.Thermal1020.Shared.litGiven
    congr 1
    let p:= heap q; let t:= heap (vital q read φ); let Y:= Mound q
    let u (i:Y):= sumFee (p i) σ; let v (i:Y):= sing (t i) σ; let u'(i:Y):= sumFee (t i) σ
    let L:=fun i:Y=> (p i).M
    let z i:= Poly.send ((FreeCensus Y).fire i) 1; let Z:= FreeCensus Y
    -- physical Leaf proof fields defeq; change common type explicitly
    have ht : (fun (i:Y)=>(t i).M)=L:=by funext i; cases i <;> rfl
    change Photo.given (S:=S) (fun i:Y=>(t i).M) u' Γ v U=_
    rw [ht]
    change Photo.given (S:=S) L u' Γ v U= (decode φ) (Photo.given (S:=S) L u Z z U)
    unfold Photo.given; rw [map_sum]; refine Finset.sum_congr rfl fun i _=> ?_
    rw [map_smul (decode φ)] -- use map_smul since Complex.ofReal
    have hh (j:Y):(leafName (fun i:Y=>(p i).s) (fun i:Y=>clipTest q read σ i φ) j*leafName (fun i:Y=>(p i).s) (fun i:Y=>clipTest q read σ i φ) j)=0:= leafName_sq (fun i:Y=>(p i).s) _ (fun i=>(p i).shiny) j
    rw [show ((decode φ) (∏ j∈ i.val, z j))= _ from RG05.Strand.paint_many _ hh free_all _ _]
    simp_rw [z, RG05.Strand.paint_knot,one_smul]
    rw [Complex.ofReal_mul,Complex.ofReal_mul,← smul_smul,← smul_smul]; congr 1
    rw [Complex.ofReal_prod,Complex.ofReal_prod]
    rw [← Finset.prod_smul,← Finset.prod_smul]; apply Finset.prod_congr rfl; intro j hj
    rw [show (↑(u' j):ℂ) • v j= _ from Menu.purchase _ hx]; change Poly.send _ _= (↑(sumFee (heap q j) σ):ℂ) • _
    rw [leafName,Menu.sent,pays_clip q read σ hx]; rcases j with j|j <;> rfl -- need prod_smul theorem

lemma forwarded (S:StepData c f){a b e v x:ℝ}(h:R.Lawful a b v x e)(hK:S.IsKernel R.beta G) (hdr:V→(V→T)→ℂ)(φ:V→T):
    S.push R.beta (offered q read hdr φ)= fun U=> Poly.pass (Mach Γ (fun i=>hdr i φ))* (decode φ) (S.push R.beta (counts0 q σ S) U):=by
    let g₀:= counts0 q σ S
    let F:= decode φ; let f:= F.toContinuousLinearMap.restrictScalars ℝ
    let Y:= fun U=> F (g₀ U); let x:= Poly.pass (Mach Γ (fun i=>hdr i φ))
    rw [funext (counted q read σ hx S h hdr φ)];
    have he:= counts_integrable q σ S h
    funext U
    rw [Menu.convective (Y:=Y) S x R.beta hK (f.integrable_comp he)]
    unfold StepData.push
    apply congr_arg (x*·)
    have hp:= f.integral_comp_comm (StepData.push_slice hK U _ he)
    simp_rw [f.map_smul] at hp
    exact hp
end YM.FVA1.MenuBridge
