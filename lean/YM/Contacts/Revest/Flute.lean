import YM.Contacts.Revest.Hybrid
import YM.Contacts.Poetry.Plash
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Revest
open AnalyticBridge VerifiedReset Collection
open PhysicalNext.Repeat Terrain
open Function Filter Set Lattice Wilson RG Pressure Ovens Ovens.Pipes Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration
open Push.AbsoluteSums Animals
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}{n : Side}{R:PathData G}{c:Clip}{p:BudgetPoint}{H w δ γ α : ℝ}{X:Pipes G n}{d:Tap G n}
namespace Flute
abbrev extendP (p:BudgetPoint) (x:Site n): RegularAddress n:= ⟨x,neighbors p.B x,(neighbors_mem ..).mpr (by rw [separation_self]; omega)⟩
structure Salary (p:BudgetPoint) (f:Trio.Offer G n) (C:ℝ) : Prop where
   move_ : Trio.Mirrors f
   bill x : p.Regular (neighbors p.B x) (f x)
   zen x : f x 1=0
   erase x : Nonwrapping (neighbors p.B x) x → ∀ a b,IsAffineDirection x a → IsAffineDirection x b → logHessian (f x) a b=0
   tariff : ∃ g:Site n→ℝ, (∀ x,p.supBounds x (neighbors p.B x) (f x) (g x))∧ Quotes.anchored p (extendP p) g C
variable (X) (p)
-- prepend site terms
local notation "N" => numbering (Site n ⊕ ℕ)
def put (X:Pipes G n) (p:BudgetPoint): Pipes G n:= { X with reg:= Sum.elim (extendP p) X.reg ∘ (N) }
def lay (f : Trio.Offer G n) (d:Tap G n): Tap G n:={d with regular:= Sum.elim f d.regular ∘ (N)}
-- capital
variable {X p}{f:Trio.Offer G n}
variable (hp:Salary p f H)
include hp
lemma welcomes (hv:(X.pours d).RegularFamily p): ((put X p).pours (lay f d)).RegularFamily p:= by
  let x (i:Site n ⊕ℕ):= Sum.elim (extendP p) X.reg i; let y := Sum.elim f d.regular
  have hi (i:Site n ⊕ℕ): p.Regular (x i).support (y i)∧y i 1=0 ∧ (Nonwrapping (x i).support (x i).site → ∀ a b, IsAffineDirection (x i).site a→ IsAffineDirection (x i).site b→ logHessian (y i) a b=0):= by
    rcases i with i|i; exact ⟨hp.bill _,hp.zen _,hp.erase _⟩; exact ⟨hv.smooth i,hv.at_flat i,hv.vanish i⟩
  exact ⟨fun i=>(hi _).1,fun i=>(hi _).2.1,fun i=>(hi _).2.2⟩
lemma dance {q b} (he:(X.pours d).Moves q b):Nonempty (((put X p).pours (lay f d)).Moves q b):= by
   let W:= Meadow.spin (q,b); let π := Equiv.sumCongr W he.ep; let A:=(put X p).pours (lay f d); let z:= (N); let Q:= (z.trans π).trans z.symm; let C (i:Site n⊕ℕ):=Sum.elim (extendP p) X.reg i; let F:=Sum.elim f d.regular
   have hz(i): z (Q i)=π (z i):= z.apply_symm_apply _
   have he' i: (C (π i)).site=affine q b (C i).site∧(C (π i)).support=(C i).support.image (affine q b) ∧ ∀ U,F (π i) U=F i (pull q b U):= by
     rcases i with i|i; · exact ⟨rfl, Marlin.moverz (q,b) p.B i,fun U=> (hp.move_ i q b U).symm⟩
     exact ⟨he.reg_site _,he.reg_support _,he.valuesE _⟩
   refine ⟨Q,he.kp, ?_,?_,he.forced_support,he.forced_inventory,he.forced_tests,?_,he.valuesK⟩
   · intro i; change (C (z (Q i))).site=_; rw [hz]; exact (he' _).1
   · intro i; change (C (z (Q i))).support=_; rw [hz]; exact (he' _).2.1
   intro i U; change F (z (Q i)) U=_; rw [hz]; exact (he' _).2.2 _
lemma height (ht:Ingredients X d p δ γ): Ingredients (put X p) (lay f d) p (H+δ) γ := by
   obtain ⟨κ,b,u,hX,hx,hE⟩:=ht.pays; let Y:=put X p; let t:=lay f d; let w:=hX.stamp; obtain ⟨c,hc,hC⟩:=w.boundE; obtain ⟨s,hs,hS⟩:= hp.tariff
   have h : (Y.pours t).EBound p (H+δ) := by
     let g:= Sum.elim s c; let X' :=Sum.elim (extendP p (n:=n)) X.reg; let f' := Sum.elim f d.regular; have ht i:p.supBounds (X' i).site (X' i).support (f' i) (g i):= by rcases i with i|i; exact hs i; exact hc i
     refine ⟨g∘ (N), fun i=>ht ((N) i),fun o=>Cost.equiv (N) (Cost.sum (f:=fun i:Site n ⊕ℕ => if (X' i).site=o then p.mass (X' i).support (g i) else 0) (hS o) (show SumBudget _ δ from hC o))⟩
   have hv:(Y.pours t).ForcedFamily p:= ⟨w.forced.sym,w.forced.symtest,w.forced.meas,w.forced.meas_test,w.forced.reads,w.forced.reads_test,w.forced.permit⟩
   refine ⟨κ,b,u,⟨⟨welcomes hp w.regular,hv,fun q b=>dance hp (w.moves q b).some,h,w.boundK⟩,hX.visits,hX.pays,hX.steady,hX.looks,hX.reads,hX.carries⟩,⟨hx.margin,hx.certificate⟩,hE⟩
omit hp in
def film (p:BudgetPoint) (f:Trio.Offer G n) (U:Config G n):=∑ i, masked p.threshold (neighbors p.B i) (f i) U
omit hp
lemma covers (h:Ingredients X d p δ γ)(β τ:ℝ) (U:Config G n): (trunk R c p (put X p) (lay f d) β τ).eval U=(trunk R c p X d β τ).eval U * Real.exp (-film p f U):= by
   obtain ⟨_,_,_,he,h⟩:= h.pays; let A:= (X.pours d); let Y:= (put X p).pours (lay f d); let C:= Sum.elim (extendP p (n:=n)) X.reg; let F:= Sum.elim f d.regular; let P i := masked p.threshold (C i).support (F i) U; have ht:Y.additive p U=film p f U+A.additive p U:= by
     change ∑' i,P ((N) i)=_; rw [(N).tsum_eq P,Summable.tsum_sum (f:=P) Summable.of_finite ((Activities.ESeries he.stamp).summable U),tsum_fintype]; rfl
   unfold Progress.DirectedRecipe.trunk Rep.eval Rep.exponent; dsimp only; change _ * Y.gas p U=_* (A.gas p U)* _; rw [ht,mul_right_comm _ _ (Real.exp _),← Real.exp_add]; apply congr_arg₂ _ (congr_arg Real.exp (by ring)) rfl
local notation "X'" => put X p
local notation "f'" => lay f d
def token (X:Pipes G n) (p:BudgetPoint): Site n ↪ ℕ where
  toFun i:= Rack.upE (put X p) ((N).symm (.inl i)); inj' _i _j h:= Sum.inl_injective ((N).symm.injective ((Rack.upE (put X p)).injective h))
variable (X p)
lemma purchase (x:Site n) : (drawer G n).reg (token X p x)= extendP p x:= by
    change (drawer ..).reg (Rack.upE (X') _)=_; rw [Rack.reg_up]; unfold put; dsimp only [Function.comp_apply]; rw [Equiv.apply_symm_apply]; rfl
-- fit model label
variable (f d R c)(β τ:ℝ)
local notation "K" => finish R c p (put X p) (lay f d) β τ
def solo : Poetry.Lecturer (K) p.B:= ⟨token X p, fun i=>congr_arg RegularAddress.site (purchase p X i),fun i=>congr_arg RegularAddress.support (purchase p X i)⟩
lemma lights (x:Site n): (K).activities.E ((solo R c p X d f β τ).place x)=f x:= by
   change stuff (Rack.upE (X')) ( f'|>.regular) ((Rack.upE (X')) _)=_
   rw [stuffed]; unfold lay; dsimp only [Function.comp_apply]; rw [Equiv.apply_symm_apply]; rfl
include hp
lemma trumpet (hv: Ingredients X d p δ γ) : let k:=solo R c p X d f β τ; Toll (K) (Poetry.unknown k) (H+δ) δ:= by
   let V:= (K); let A:= V.activities; let B:= token X p; let T:= Rack.upE (X'); let Y:= (drawer G n).pours (Rack.widen (X') (f')); let W:=(X'|>.pours f'); let Z:=(X.pours d); have he:= Rack.preserves (X') (f') p; intro k; obtain ⟨_,_,_,ht,-,-⟩:= hv.pays; obtain ⟨z,hz,hT⟩:= ht.stamp.boundE; obtain ⟨u,hu,hw⟩:= hp.tariff
   let y:= Sum.elim u z; let L:=(N); let v:=y ∘ L; have hv (i) : p.supBounds (W.reg i).site (W.reg i).support (W.E i) (v i) := by
       let C:= Sum.elim (extendP p (n:=n)) X.reg; let U:= Sum.elim f d.regular; have h i : p.supBounds (C i).site (C i).support (U i) (y i) := by rcases i with i|i; exact hu _; exact hz i
       exact h (L i)
   let Xs:Site n⊕ℕ→RegularAddress n:= Sum.elim (extendP p (n:=n)) X.reg
   refine ⟨stuff T v, show ∀ i,p.supBounds (Y.reg i).site (Y.reg i).support (Y.E i) (stuff T v i) from fun i=>?_, show anchored p Y.reg (stuff T v) _ from fun x=> transfer_budget T ?_ ?_ (show SumBudget (fun i=> if (W.reg i).site=x then p.mass (W.reg i).support (v i) else 0) (H+δ) from Cost.equiv (N) (Cost.sum (f:=fun i:Site n⊕ℕ=> if (Xs i).site=x then p.mass (Xs i).support (y i) else 0) (hw x) (hT x))), show anchored p Y.reg (selectK (Poetry.unknown k) *stuff T v) _ from fun x=>?_⟩
   · by_cases hi:i∈Set.range T
     · obtain ⟨q,rfl⟩:=hi; erw [he.same_reg,he.emits,stuffed]; exact hv _
     erw [he.restE i hi, blank _ _ hi]; exact no_cost ..
   · intro i; erw [stuffed,he.same_reg]
   · intro i hi; rw [blank _ _ hi]; simp [BudgetPoint.mass]
   let s:Site n⊕ℕ→ℝ:= Sum.elim (fun _=>0) z; let K' i:=if (W.reg i).site=x then p.mass (W.reg i).support (s ((N) i)) else 0
   have hh : SumBudget K' δ:= by
      let Xs:Site n⊕ℕ→RegularAddress n:= Sum.elim (extendP p (n:=n)) X.reg; let K' :Site n⊕ℕ→ℝ := fun i=>if (Xs i).site=x then p.mass (Xs i).support (s i) else 0
      let a1:Site n→ℝ:= K' ∘ Sum.inl; have hc: ∀ i,a1 i=0:=fun i=>by dsimp [a1,K',s,BudgetPoint.mass]; split <;> ring
      have hC:SumBudget a1 0:= by rw [funext hc]; simp [SumBudget]
      apply Cost.equiv (N) (f:=K'); simpa only [zero_add] using Cost.sum (f:=K') hC (hT x)
   refine transfer_budget T (fun i=>?_) ?_ hh
   · have he':Poetry.unknown k (T i) ↔ ∀ x,L i≠ .inl x:= by
       unfold Poetry.unknown; constructor
       · rintro h x hx; exact h ⟨x,show T (L.symm (.inl x))=T i from congr_arg (fun i=> T i) (L.symm_apply_eq.mpr hx.symm)⟩
       rintro h ⟨x,hx⟩; apply h x; rw [← T.injective (show T (L.symm (.inl x))=T i from hx),Equiv.apply_symm_apply]
     have ht: selectK (Poetry.unknown k) (T i)*v i=s (L i):= by unfold selectK; dsimp [v,Function.comp_apply]; rw [propext he']; cases L i <;> simp [y,s]
     erw [Pi.mul_apply,stuffed,he.same_reg]; rw [ht] -- mod
   intro i hi; rw [Pi.mul_apply, blank _ _ hi, mul_zero]; simp [BudgetPoint.mass]
end Flute
end YM.Contacts.Revest
