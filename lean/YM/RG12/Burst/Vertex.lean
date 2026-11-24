import YM.RG12.Burst.Twice
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mercury.Debonaire
import YM.RG12.Burst.Feder
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Blush
open Function Filter Lattice RG Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ovens ConnectedActivityE6 Daisy Daisy.Charity Mallow Lotus
open PowerSeries Extra.Histories Progress.DirectedRecipe Next.Foundations Precision
open Blaze Blaze.March Poll Pond Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c f n: Side}
variable {i j:ℕ} {o: Site n}{S:Support n}{B : BudgetPoint}
open Pressure Push.SectorMeasure Greenbelt Refrain
variable {S:StepData c f}{T: Tube G S}{L:Side}{P:Teller G} {Q: ConnectedActivityE6.Target G P}{W x μ C : ℝ}{o':Target.Order G W}{R:RG.Rep G f}
variable (H:Cash W x μ L Q o' C T R) (r : Cloud R) (o : Site c)
local notation "hd"=> r.live
local notation "hd'"=> r.pale
local notation "χ"=> Chi.canonical
variable (K R' : ℝ → Code G c)
variable (v: ℂ)
variable (F : YM.Labels.Frame G j)
section prices
local notation "M" => Blush.screen H r K R' v F
variable {R2 : Rep G c} (he:R2.p=B)
variable {A b q t d Y f₀ α k β e w t':ℝ}{n' ℓ:ℕ}(N: Captain H n' q t d Y A b t' f₀ k ℓ Chi.canonical)
namespace Burst10
open Daisy.Charity.RG12 Matter Height Shield Stained
-- Drop packets by markSeed(derived on algebra not parity). Drop K explicitly because roster incidence. No generic subtraction. Then in warm molecules only Miniature and Signed Cubic. Horn criterion employed.
section masks
open Source Labels
variable (g:Hol G)
set_option quotPrecheck false
local notation "u" => rows10 (B:=B) H r o v F g
local notation "w" => warm11 (B:=B) H r o v F g
local notation "Tag" => r.live.turn.badge S

lemma pristine {i:H.fragrances}{k:ℕ}(hk:r.live.turn=.logKey k)(hw: w i ≠0)(ht:hue H i=1): i=Brim.icon H k:=by
    obtain ⟨hP,⟨x',hx,hQ⟩,h⟩:= guides11 H r o v F g hw; rw [ht] at hP
    have hJ:i.1=0:=by omega
    obtain ⟨a,ha⟩:∃ a,i=chip H a:=⟨_,single H i hJ⟩; subst i
    have hT : a.val.card=1 := by unfold hue chip at ht; simpa only [Fintype.sum_subsingleton _ none] using ht -- find name
    have hn : a.val={Tag}:=(card_eq_one.mp hT).elim (fun i h=> h.trans (congr_arg _ (mem_singleton.mp ((h ▸ hx): Tag∈ ({i}:Finset (Head S)))).symm))
    rw [hk] at hn; exact congr_arg (chip H) (Subtype.ext hn)
lemma warming {k:ℕ}(hk:r.live.turn=.logKey k): w (Brim.icon H k) = Local.weighted g F o (Brim.plate H k).support B.threshold (pane H r v (Brim.icon H k)):=by
    let p:=Brim.icon H k; have hf:hue H p=1:=by unfold hue p Brim.icon Brim.once; simp [Brim.head]
    have hp:Height.overlap H p=0:=by unfold Height.overlap Cash.numP p Brim.icon Brim.once; simp [Push.AbsoluteSums.Mixed.shares,Brim.head];rfl
    have he := Mercury.grinchY H r.live k hk o
    unfold warm11 rows10; rw [if_neg,he]
    unfold Daisy.Charity.RG12.cold; change ¬((3≤hue H p∨Height.overlap H p≠0)∨ _≥sign11 _+1∧ 2≤hue H p)
    simp [hf,hp]

-- sharply classified demand; either one 2-molecule (contains mark & one χ lighting), or pair of singletons (one mark, one same χ lighting). Hue counts occurrences; in latter two clusters distinct as addresses? needn't be, but classification says mark k and bulb of two different LOG TYPES so yes. No packets/Box or previous E.K labels.Sector histories may choose anywhere. No L assumptions.
structure Duo (r:Cloud R) (p:H.fragrances):Prop where
   citizen :
    (∃ s:H.ThinP, ∃ h:Head S,p=chip H s ∧ s.val={r.live.turn.badge S,h} ∧ r.live.turn.badge S ≠h ∧ bulb h) ∨
    (∃ (b: Option (Fin p.1))(h:Head S), p.1=1∧ (p.2 b).val={r.live.turn.badge S} ∧ bulb h ∧ ∀ a:Option (Fin p.1), a≠b→ (p.2 a).val={h})
   reaches: Height.overlap H p=0
   price: hue H p=2
private lemma spouse (p:Wing): ¬bulb (p.badge S):=by
   intro hp; rcases hp with ⟨t,h⟩|⟨t,h⟩ <;> cases p <;> simp [Wing.badge,cubeHead,miniHead] at h
private def tt (i:Option (Fin 1)):Option (Fin 1):= if i.isNone then some 0 else none
private lemma tz(i:Option (Fin 1)): tt i≠ i ∧ ∀ j:Option (Fin 1),j≠i→j=tt i:=by
   cases i with
   | none => refine ⟨by simp [tt],fun j h=>?_⟩; cases j <;> simp_all [tt,Subsingleton.elim (_:Fin 1) (0:Fin 1)]
   | some x=> have H(a:Fin 1):a=0:=Subsingleton.elim ..; constructor; · simp [tt]
              intro j; cases j <;> simp [tt,H]
set_option maxHeartbeats 640000 in
lemma twigs11 (k:ℕ)(hk:r.live.turn=.logKey k)(p:H.fragrances)(hp:p≠Brim.icon H k)(hw:w p≠0): Duo H r p:=by
   have ht:= guides11 H r o v F g hw; have hP:=ht.fields
   have he:hue H p=2:= by
       by_contra h; have he:hue H p=1:=by omega
       exact hp (pristine H r o v F g hk hw he)
   refine ⟨?_, not_not.mp (fun h=>hw (if_pos (Or.inl (Or.inr h)))),he⟩
   obtain ⟨u',hU,hμ⟩:=ht.choice; have hv:p.1=0 ∨ p.1=1:=by omega
   rcases hv with hv|hv
   · left; obtain ⟨a,h⟩:∃ a:H.ThinP,p=chip H a:=⟨_,single H p hv⟩; subst p
     have hT : a.val.card=2 :=by unfold hue chip at he; simpa only [Fintype.sum_subsingleton _ none] using he
     obtain ⟨i,j,hij,hZ⟩:= Finset.card_eq_two.mp hT; change Tag∈ a.val at hU; rw [hZ] at hU
     have hh: Tag=i∨Tag=j:=by simpa only [Finset.mem_insert,Finset.mem_singleton] using! hU
     have hi(t:Head S)(ht:t∈ ({i,j}:Finset _))(h:t ≠ Tag) := (hμ u' t ((hZ.symm ▸ ht): t∈a.val)).resolve_left (fun hh=>h hh.2)
     rcases hh with H' | H'
     · rw [← H'] at hZ; exact ⟨a,j,rfl,hZ,H'.symm ▸ hij,hi j (by simp) (H'.symm ▸ Ne.symm hij)⟩
     rw [← H'] at hZ; refine ⟨a,i,rfl,?_,H'.symm ▸ Ne.symm hij,hi i (by simp) (H'.symm ▸ hij)⟩; rw [hZ]; ext; simp [or_comm]
   right
   rcases p with ⟨n,p⟩; change n=1 at hv; subst n
   change (∑ i:Option (Fin 1), (p i).val.card)=2 at he
   have hh(p:H.ThinP):1≤ p.val.card:= Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (by obtain ⟨uA,ht⟩:= p.2.1; intro hh; change uA∈ p.val.biUnion H.supportP at ht; rw [hh] at ht; simp at ht))
   simp only [Fintype.sum_option] at he; simp only [Fintype.sum_unique] at he
   let mate:=tt u'; have hl:mate≠u':=(tz u').1; have hz:= (tz u').2
   have hc(i:Option (Fin 1)):(p i).val.card=1:=by
        have h1:=hh (p none); have h2:=hh (p (some default)); cases i with
        | none=>omega
        | some j=>rw [Subsingleton.elim j default]; omega
   have hT : (p u').val={Tag}:=(card_eq_one.mp (hc u')).elim (fun i h=> h.trans (congr_arg _ (mem_singleton.mp ((h ▸ hU): Tag∈ ({i}:Finset (Head S)))).symm))
   obtain ⟨hV,hv⟩:=card_eq_one.mp (hc mate)
   have hm:= (hμ mate hV (show hV∈ (p mate).val from by rw [hv]; simp)).resolve_left (fun h=>hl h.1.symm)
   exact ⟨u',hV,rfl,hT,hm,fun x hx=> hz x hx ▸ hv⟩

end masks
end Burst10
end prices
end YM.PhysicalNext.Repeat.Blush
