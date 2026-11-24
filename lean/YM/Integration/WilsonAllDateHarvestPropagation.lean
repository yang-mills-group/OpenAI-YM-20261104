import YM.Integration.WilsonAllDateHarvestStability
import YM.Integration.WilsonAllDateHarvestEndpointIntegrability

/-! At the actual reporting step, retain the scalar and all singleton old gas
entries in both programs. Price the original regular and forced output
differences at the original receiving support exponent and marker weights. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestPropagation

open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker MergeProof
open MergeProof.Accent MergeProof.Menu RG05Readout RG05Readout.Many RG05Readout.Address
open Extra.Histories Push Ac GridApprox.Nil Local Extra.Trajectories Extra.Multi
open WilsonAllDateHarvestAffine WilsonAllDateHarvestLedger WilsonAllDateHarvestStability
open scoped BigOperators Classical

variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {J:Census V}
variable {n:Side} {K Y:Type*}

def scaled (z:ℂ) (F:K→Y→Poly J) (s:K) (U:Y) : Poly J := z • F s U

variable {w:V→ℝ} {F:K→Y→Poly J} {B:ℕ} {k:K→Support n} {a d:ℝ}

omit [Fintype V] in
private theorem scale (z:ℂ) (h:Towed w k F B a d) :
    Towed w k (scaled z F) B a (‖z‖*d) := by
  change Towed w k (fun i U=>z • F i U) B a (‖z‖*d)
  simpa only [linear,zero_smul,add_zero,norm_zero,zero_mul] using towed h h z 0

omit [Fintype V] in
/-- Spend the full, unit-radius date purchase on any positive course radius at
most one. The same nonnegative major is valid before every held field. -/
theorem atRadii (hw:∀i,0<w i) (fit:∀i,w i≤1)
    (h:Towed (fun _:V=>1) k F B a d) : Towed w k F B a d := by
  obtain ⟨major,hm,hb,hc⟩:=h
  refine ⟨major,hm,hb,?_⟩
  intro i
  obtain ⟨v,nn,me,spent⟩:=hc i
  refine ⟨v,nn,me,le_trans ?_ spent⟩
  unfold wordsPrice
  apply Finset.sum_le_sum
  intro q _
  apply mul_le_mul_of_nonneg_right _ (nn q)
  unfold Poly.toll
  exact Finset.prod_le_prod (fun i _=>(hw i).le) (fun i _=>fit i)

variable {o:V→Site n} {H:Support n→ Config G n→Poly J} {T:Box n→ Config G n→Poly J}

omit [Fintype V] in
private theorem legal (z:ℂ) (h:Carton o H T a) : Carton o (scaled z H) (scaled z T) a := by
  change Carton o (fun i U=>z • H i U) (fun i U=>z • T i U) a
  simpa only [linear,zero_smul,add_zero] using carton h h z 0

def density (P:Rep G n) (rows:V→Address.Three G n) (H:Support n→ Config G n→Poly J)
    (T:Box n→ Config G n→Poly J) : Config G n→Poly J :=
  restore P (fun i=>(rows i).2.1) (fun i=>profile P.activities (rows i).2.2) H T

omit [Fintype V] in
theorem measured {f v:Side} (S:StepData v f) (β:ℝ) (hk:S.IsKernel β G)
    {X Y:Config G f→Poly J} (hx:Integrable X (prior G f)) (hy:Integrable Y (prior G f))
    (z:ℂ) : S.push β (fun U=>blend (X U) (Y U) z) =
      fun U=>blend (S.push β X U) (S.push β Y U) z := by
  have sc (b:ℂ) (F:Config G f→Poly J) : S.push β (b • F)=b • S.push β F := by
    funext U
    change (∫ u,S.density β u U • (b • F u) ∂prior G f) =
      b • ∫ u,S.density β u U • F u ∂prior G f
    simp_rw [smul_comm _ b,integral_smul]
  simp only [blend_eq,linear]
  change S.push β ((1-z) • X + z • Y)=(1-z) • S.push β X + z • S.push β Y
  rw [StepData.push_add hk _ _ (hx.smul _) (hy.smul _),sc,sc]

variable {A:History G} {N m p:ℕ} {r:ℕ→ℕ} {b c:ℝ}
set_option quotPrecheck false
local notation "fine" => A.rep N p (m+1)
local notation "coarse" => A.rep N p m
local notation "step" => A.levels.clock.op m p
local notation "f" => A.S.side (m+1) p
local notation "v" => A.S.side m p
local notation "α₁" => (A.levels.budget (m+1)).supportExponent
local notation "α₀" => (A.levels.budget m).supportExponent
variable {D:GaugeDoor (A.rep N p (m+1)) (A.rep N p m)}
variable {I:V→Address.Three G (A.S.side (m+1) p)} {Q:V→Address.Three G (A.S.side m p)}
variable {x:V→Site (A.S.side (m+1) p)} {w' l:V→ℝ}
variable {H':Support (A.S.side (m+1) p)→ Config G (A.S.side (m+1) p)→Poly J}
variable {K':Box (A.S.side (m+1) p)→ Config G (A.S.side (m+1) p)→Poly J}
variable {ν:V→ℂ}
local notation "Q₀" => fun i:V=>(ν i)⁻¹ • Q i

/-- Admit both original dated input densities before opening the restricted
census and replaying the physical lower history. -/
theorem endpoints (course:Coursework A r D a b c) (sel:A.Selected) (hm:m<N)
    (cap:WilsonAllDateHarvestAffine.Three J) (hw:∀i,0<w i) (fit:∀i,w i≤1)
    (cost:∀i,2*w i*l i≤1) (hν:∀i,1≤‖ν i‖)
    (rides:∀i,Ride step (x i) ((step).ratio.parent (x i)) D (ν i) (I i) (Q i) (l i))
    (ho:Occupancy x (r m)) (δ:ℝ) (hδ:0<δ)
    (marks:Carton x H' K' (fine).p.threshold)
    (regular:Towed (fun _:V=>1) id H' (fine).p.B (α₁-1) δ)
    (forced:Towed (fun _:V=>1) Prod.fst K' (fine).p.B (α₁-1) δ) :
    let X:=fun z:ℂ=>density fine I (scaled z H') (scaled z K')
    MenuBoard fine I (X 0) x w (α₁-1) 1 ∧
    MenuBoard fine I (X (δ:ℂ)⁻¹) x w (α₁-1) 1 ∧
    density fine I H' K'=fun U=>blend (X 0 U) (X (δ:ℂ)⁻¹ U) (δ:ℂ) := by
  let X (h:ℂ) := density fine I (scaled h H') (scaled h K')
  have normδ : ‖(δ:ℂ)‖=δ:=by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
  have nonzero : (δ:ℂ)≠0:=by exact_mod_cast hδ.ne'
  have ride1 (i:V) : Ride step (x i) ((step).ratio.parent (x i)) D 1 (I i) (Q₀ i) (l i) := by
    have h:=(rides i).matchPay 1 (ν i)⁻¹ 1 (show _=_ by
      rw [inv_mul_cancel₀,one_mul]
      exact norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (hν i)))
    rw [one_smul,norm_one,norm_inv,max_eq_left (inv_le_one_of_one_le₀ (hν _)),one_mul] at h
    exact h
  have admit (z:ℂ) (hz:‖z‖*δ≤1) : MenuBoard fine I (X z) x w (α₁-1) 1 :=
    WilsonAllDateHarvestEndpointIntegrability.original course sel hm hw ride1 ho cost
      ⟨_,_,legal z marks,(scale z (atRadii hw fit regular)).shrink le_rfl hz hw,
       (scale z (atRadii hw fit forced)).shrink le_rfl hz hw,rfl⟩
  let t:ℂ := (δ:ℂ)⁻¹
  have low:=admit 0 (by simp)
  have top:=admit t (by simp only [t,norm_inv,normδ,inv_mul_cancel₀ hδ.ne',le_rfl])
  have ident : (fun U=>blend (X 0 U) (X t U) (δ:ℂ))=density fine I H' K' := by
    funext U
    let p:=legal 0 marks
    let q:=legal t marks
    change blend (restore _ _ _ _ _ U) (restore _ _ _ _ _ U) _=_
    rw [← WilsonAllDateHarvestAffine.original _ _ _ cap (fun i=>(p.exp i).2)
      (fun i=>(q.exp i).2) (fun i=>(p.flag i).2) (fun i=>(q.flag i).2)]
    simp only [scaled,blend,zero_smul,sub_zero,smul_smul,t,mul_inv_cancel₀ nonzero,one_smul,zero_add,density]
  exact ⟨low,top,ident.symm⟩

theorem original (course:Coursework A r D a b c) (sel:A.Selected) (hm:m<N)
    (cap:WilsonAllDateHarvestAffine.Three J) (hw:∀i,0<w i) (fit:∀i,w i≤1)
    (cost:∀i,2*w i*l i≤1) (hν:∀i,1≤‖ν i‖)
    (rides:∀i,Ride step (x i) ((step).ratio.parent (x i)) D (ν i) (I i) (Q i) (l i))
    (ho:Occupancy x (r m)) (hp:Occupancy ((step).ratio.parent ∘ x) (r m))
    (hpos:∀i,0<w' i) (repeg:Repegs ((step).ratio.parent ∘ x) (A.levels.budget m).B
      (fun i=>a*w i) w' (1/2) 1 J)
    (δ:ℝ) (hδ:0<δ) (small:δ≤1)
    (marks:Carton x H' K' (fine).p.threshold)
    (regular:Towed (fun _:V=>1) id H' (fine).p.B (α₁-1) δ)
    (forced:Towed (fun _:V=>1) Prod.fst K' (fine).p.B (α₁-1) δ) :
    ∃ (P:Ledger coarse Q₀ ((step).push (fine).beta (density fine I (scaled 0 H') (scaled 0 K')))
         ((step).ratio.parent ∘ x) w' α₀)
      (T:Ledger coarse Q₀ ((step).push (fine).beta (density fine I H' K'))
         ((step).ratio.parent ∘ x) w' α₀),
      Towed w' id (fun s U=>T.H s U-P.H s U) (coarse).p.B α₀ (2*δ) ∧
      Towed w' Prod.fst (fun s U=>T.K s U-P.K s U) (coarse).p.B α₀ (2*δ) := by
  let X (z:ℂ) := density fine I (scaled z H') (scaled z K')
  let t:ℂ := (δ:ℂ)⁻¹
  obtain ⟨low,top,head⟩:=endpoints course sel hm cap hw fit cost hν rides ho δ hδ marks regular forced
  have run (z:ℂ) (h:MenuBoard fine I (X z) x w (α₁-1) 1) :=
    course.send sel hm h (by linarith only) hν hw rides ho hp cost hpos repeg
  obtain ⟨base,mid,hH,hK⟩:=output cap (run 0 low) (run t top) δ hδ.le small
  have pushed:=measured step (fine).beta (A.levels.transition_mass ..) low.cleared top.cleared (δ:ℂ)
  rw [←head] at pushed
  rw [pushed]
  exact ⟨base,mid,hH,hK⟩

end YM.Integration.WilsonAllDateHarvestPropagation
