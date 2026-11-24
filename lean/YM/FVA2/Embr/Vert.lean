import YM.FVA2.Embr.Bucks
/-!
 # Exact rereading using other tag-identification cloth installed along same epoch geometry
 Applies at every physical field and open condition, not just any formal jet.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Embr
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Finset MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade Hearth Hearth.Clan RGComparison.Core16
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge} {c f n:Side} {L:Fabric G n} (T:Cloth L)(v: Clan L)

def warmSame {n:Side}{L:Fabric G n}(T:Cloth L)(v:Clan L): Warm (install L T v)≃ Warm T:= by
 cases T with
 | floor=> exact Equiv.refl _
 | @inLayer c f S H t hf L P C=> let p:S.Choices×Clan L:=v; exact Equiv.sumCongr (Equiv.refl (Index S P)) (warmSame C p.2)
termination_by structural T
-- cast orientation natural
local notation "◎" => lowest L v
local notation "Z"=> changeTag L v
local notation "R"=> install L T v
section
variable {α: Type}
def pointsAt (L:Fabric G n)(v:Clan L) (x:OEdge (Bottom L) → α) : OEdge (Bottom (changeTag L v)) →α:= (lowest L v).symm ▸ x
-- cooled tags use this R warm coordinates; homeomorphism the pulled orientation. show all shrugs
end

def yarn : (Warm T→G.El) ≃ₜ (Warm R → G.El):= Homeomorph.piCongrLeft (Y:=fun _=> G.El) (warmSame T v).symm  -- name
lemma yarn_apply (x): yarn T v x=x ∘ warmSame T v:= by ext1 i; obtain ⟨i,rfl⟩:= (warmSame T v).symm.surjective i; simp [yarn]
lemma yarn_unit : yarn T v 1=1:= by rw [yarn_apply]; rfl

variable {S:StepData c f}{H:S.patch.Branches S.kernel G}{hf:Even f.val}{t:S.Choices}{U:Fabric G c}
variable {P:Inside S.ratio}{C:Cloth U}
local notation "Γ"=> layer S H t hf U
local notation "T0"=> Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C

lemma enlisted_first (i:OEdge f)(x:Warm T0→G.El): door T0 x (.inl i)= if h:P.Innate i then 1 else x (.inl ⟨i,h⟩):= by
 split
 next h=> exact door_tree T0 x _ ((sprig_now P (fir C) i).mpr h)
 next h=>
   let k:= Sum.inl (⟨i,h⟩: Index S P) (β:=Warm C); let j:= leeway T0 k; have he:j.val=Sum.inl i:= rfl; rw [←he, door_loop]; simp [j]; rfl

-- version of pull.Heuristics support structural
lemma parent_same {n:Side}{L:Fabric G n}(T:Cloth L)(v:Clan L)(a:LinkFrame G (Bottom L))(x: Warm T→ G.El):
 (changeTag L v).principal (rear _ (pointsAt L v a) (door (install L T v) (x ∘ warmSame T v)))= L.principal (rear L a (door T x)):= by
 cases T with
 | floor=> unfold pointsAt; rfl
 | @inLayer c f S H t hf L P C=>
   change S.Choices× Clan L at v; let b:=install L C v.2; let a0:= Cloth.inLayer (t:=v.1) (b:=H) (h:=hf) P b
   ext1 i; change door a0 _ (Sum.inl i)=door (Cloth.inLayer P C) x (Sum.inl i); rw [enlisted_first,enlisted_first]; split; rfl; rfl
-- keep right-tag expense! Need habitat R reads via v, not forcing x near trivial state.
lemma tax_books {n:Side}{L:Fabric G n}(T:Cloth L)(v:Clan L)(a:LinkFrame G (Bottom L))(x: Warm T→ G.El)(w:L.Cost→ℝ):
 (changeTag L v).installment (w ∘ accounts L v) (rear _ (pointsAt L v a) (door (install L T v) (x ∘ warmSame T v)))= Embr.taxes L w (rear _ a (door T x)) v:= by
 cases T with
 | floor=> exact zero_tax ..
 | @inLayer c f S H t hf L P C=>
   let A:= layer S H t hf L; let T:= Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C; let k:S.Choices× Clan L:=v
   let b:=changeTag L k.2; let d:=install L C k.2; let g:=layer S H k.1 hf b
   let x' (i:Warm C):= x (Sum.inr i)
   let U:= rear L a (door C x')
   let B:= rear b (pointsAt L k.2 a) (door d (x' ∘ warmSame C k.2))
   let V:= rear A a (door T x)
   let W:= rear g (pointsAt A v a) (door (install A T v) (x ∘ warmSame T v)); let τ:= w ∘ accounts A v;
   have hU : future S H t hf L V=U:= congr_arg (rear L a) (funext (fun i=> enlisted i x));
   have hB : future S H k.1 hf b W=B:= by
      let Ra:= install A T v
      let Φ : Warm Ra→G.El:= x ∘ warmSame T v
      have hC(i: Used b) : door Ra Φ (Sum.inr i)=door d (x' ∘ warmSame C k.2) i:= enlisted i Φ -- t definitional?
      exact Eq.trans (congr_arg (rear b (pointsAt A v a)) (funext hC)) (show rear b (pointsAt A v a) _ = _ from rfl)
   change g.installment τ W=w none * penalty S k.1 (A.principal V) (L.principal (future S H t hf L V))+ Embr.taxes L (w∘some) (future S H t hf L V) k.2
   rw [tax_split,hB,hU]; exact congr_arg₂ (· + ·) (congr_arg (w none * ·) (congr_arg₂ (penalty S k.1) (parent_same T v a x) (parent_same C k.2 a x'))) (tax_books C k.2 a x' (w∘some))
termination_by structural T

-- labels of subsequent hinge preserve right
lemma witnessed (a: LinkFrame G (Bottom L))(x: Warm T→G.El)(w:L.Accounts→ℝ):
 spends L w (rear L a (door T x)) v = (Z).spend (w ∘ Option.map (accounts L v)) (rear _ (pointsAt L v a) (door R (yarn T v x))):= by
   unfold spends; rw [budget_sum,yarn_apply,parent_same]; refine congr_arg₂ _ rfl ?_; exact (tax_books T v a x (w∘some)).symm
lemma actual (y:Flats G (Bottom L))(w:L.Accounts→ℝ→ℝ)(x:Warm T→G.El)(r:ℝ):
 spends L (fun i=> w i r) (committed T y r x) v= front R (w∘ Option.map (accounts L v)) (pointsAt L v y) r (yarn T v x):= by
 unfold front committed; rw [witnessed]; congr 2; exact Sect ◎ y
where
 Sect {x l:Side}(h:x=l)(y:Flats G l): (h.symm ▸ expLinks G _ (r • y) : LinkFrame G x) = expLinks G _ (r • (h.symm ▸ y:Flats G x)):= by subst h; rfl
end YM.FVA2.Embr
