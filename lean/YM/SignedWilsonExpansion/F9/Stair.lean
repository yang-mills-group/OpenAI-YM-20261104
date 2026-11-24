import YM.SignedWilsonExpansion.F9.Motion
/-!
# Priced cohort of rank points moved from the fine epoch through all levels

Each letter solving against its **own weight** at K sec. Assembled cohort
spans through requested auxiliary rank at each level. Observe actual meters
in F9 *without* changing these offshell steering frames. Purchases with a
uniform numeric chart-price X covering arities and all levels (via Tuition).
Later boundary geometry can ask for that same price independently of vote
coordinates. Note: Θ (actual threshold) not used here.
-/
set_option autoImplicit false
set_option maxHeartbeats 690000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{h p d k m c N u e i j l r q:ℕ}{F: Labels.Frames G}
variable {B M X Y z:ℝ}{s:Signed}

lemma nestedAxis (F:Frames G)(s:Signed)(p:d≤h)(i j:(F.level d).Index):
    bleached (F.level h) s.ortho (upL F p i) (upL F p j)= bleached (F.level d) s.ortho i j:=by
    unfold bleached; rw [←Frame.coords_basis,Frame.act_coords,←Frame.coords_basis,Frame.act_coords,climb, show tensor s.ortho (raiseLabel G p ((F.level d).basis j))= raiseLabel G p (Labels.tensor s.ortho ((F.level d).basis j)) from rfl,fare_up]
abbrev wt (F:Frame G h)(i:F.Index):= (F.grades i).1
lemma spectate_weight {X:Type*}[AddCommGroup X][Module ℝ X] (F:Frames G)(s:Signed)(p:d≤h)(i:(F.level d).Index)(he:wt (F.level d) i=d)(Y:(F.level h).Index→ X)(Z:(F.level d).Index→ X)(hZ:∀ j, wt (F.level d) j=d→ Z j=Y (upL F p j)):
     (∑ j,bleached (F.level h) s.ortho j (upL F p i) • Y j)=∑ j, bleached (F.level d) s.ortho j i • Z j:=by
    let T:= Finset.univ.image (upL F p); rw [← Finset.sum_subset (Finset.subset_univ T)]; swap
    · intro j _ hj; rw [bleach_sparse _ _ _ _ ?_,zero_smul]; intro q; have hp : wt (F.level h) j=d:= by rw [up_grade] at q; exact (congr_arg Prod.fst q).symm.trans he
      exact hj (Finset.mem_image.mpr ⟨_,Finset.mem_univ (downL F p j hp.le),up_down F p j hp.le⟩)
    unfold T; rw [Finset.sum_image (up_faith F p).injOn]; apply Finset.sum_congr rfl; intro j _; rw [nestedAxis]; by_cases hy: wt (F.level d) j=d; · rw [hZ j hy]
    rw [bleach_sparse _ _ _ _ (fun h=> hy ((congr_arg Prod.fst h).symm.trans he)),zero_smul,zero_smul]

abbrev Council (F:Frames G):=∀ h,SectionData (F.level h)
abbrev TowerP (F:Frames G):=∀ h,SourceP (F.level h)
variable {H:Hol G}{F:Frames G}{Q:Council F}{P:TowerP F}
structure Stair (Q:Council F)(P:TowerP F)(A:Levels G)(Ñ:ChartRatio G)(m c N h p k u:ℕ)(X:ℝ): Prop where
    charm (d:ℕ): d≤h →Chartage (Q d) A Ñ m c N k u p X
    supply (d:ℕ):d≤h→ Palette (F.level d) (P d) k u p X
-- avoid flattened comparisons: own-cap
namespace Stair
variable (u':Stair Q P A Ñ m c N h p k u X)
abbrev hAxis (p':d≤h)(i:(F.level d).Index): Era G ℝ:= loft (u'.supply d p') (u'.charm d p') i
def personal (l:ℕ)(p':d≤h)(i:(F.level d).Index): Era G ℝ:= pier A Ñ N d k c l (u'.hAxis p' i)
def ladder (l:ℕ)(i:(F.level h).Index): Era G ℝ:= u'.personal l ((F.level h).bound i) (downL F ((F.level h).bound i) i le_rfl)
lemma on_ladder (p':d≤h)(l:ℕ)(i:(F.level d).Index)(he:wt (F.level d) i=d): u'.ladder l (upL F p' i)=u'.personal l p' i:=by
    let H:= F.level h; let P:= upL F p' i; have hh : wt H P=d:= (congr_arg Prod.fst (up_grade F p' _)).trans he
    change u'.personal _ (H.bound P) (downL F _ P (le_refl (wt H P)))=_
    suffices h : ∀ (d':ℕ)(q:wt H P=d')(v:d'≤h), u'.personal l v (downL F v P q.le)=u'.personal l p' i from h (wt H P) rfl _ -- pass
    intro a v hp; obtain rfl:= v.symm.trans hh; rw [show downL F p' P _=i from up_faith F p' (up_down F p' P v.le)]
lemma funding (H:Hol G)(hl:m≤ l)(hv:l≤ c)(i:(F.level h).Index): Auth k (u'.ladder l i):= by let d':=(F.level h).bound i; let v:= u'.charm _ d'; exact piered v.simple v.ratios hv v.cap ((u'.supply _ d').mix _)
include u'
lemma rotated (t:∀ d≤h,MotionP (F.level d) s (P d)) (H:Hol G) (a:m≤ l)(v:l≤ c): MotionP (F.level h) s (u'.ladder l):=by
    intro i; let H':=F.level h; set d:= wt H' i; have hp:d≤ h:= H'.bound _; set j:=downL F hp i (le_refl d); have hz:wt (F.level d) j=d:= congr_arg Prod.fst (down_grade F hp i (le_refl _))
    set x:=upL F hp j; have hx:x=i:= up_down ..
    have he : Roll s (u'.personal l hp j) (∑ i, bleached (F.level d) s.ortho i j • u'.personal l hp i):=by
        let v':=u'.charm d hp; let P':= u'.supply d hp; have h (i:(F.level d).Index):Auth k (u'.hAxis hp i):= P'.mix _; let Y:=bleached (F.level d) s.ortho; unfold personal; rw [← pier_sum v'.simple v'.ratios v v'.cap _ (fun i=> Y i j) (fun i=>u'.hAxis hp i) (fun i _=> h i)]; exact (loft_seen H P' v' (t d hp) j).piere v v'.cap v'.simple v'.ratios (h j) (Auth.sum (fun i _=>(h i).μ _))
    have hv: Roll s (u'.ladder l x) (∑ b:H'.Index, bleached H' s.ortho b x • u'.ladder l b):= by unfold x; rw [on_ladder u' hp l j hz, spectate_weight F s hp j hz (u'.ladder l) (u'.personal l hp) (fun i h=>(on_ladder u' hp l i h).symm)]; exact he
    exact hx ▸ hv
-- Output points always measured at own d (from THIS same root address)
lemma principal (H:Hol G)(q:m≤ l)(t:l≤ c)(i j: TagIx (F.level h) r)(w:wT (F.level h) i≤wT (F.level h) j):
    row (F.level h) (((u'.ladder l j.val).2) 0 r) i= if i=j then 1 else 0:=by
    let T:=F.level h; let d:= wT T j; have hp:d≤h:= T.bound _; let x:TagIx (F.level d) r:=downT F hp j (le_refl d); have ht:wT (F.level d) x=d:= congr_arg Prod.fst (down_grade F hp j (le_refl _)); let y:= downT F hp i w
    let X:=u'.ladder l j.val; let Z:=u'.personal l hp x.val; have hx:X=Z:=rfl; let v:= u'.supply d hp; let a:=u'.charm d hp
    have hw: row T (Z.2 0 r) (upT F hp y)= Pi.single (M:=fun _=>ℝ) x 1 y:= (row_handed H F (P:=Z) (u'.funding H q t j) y hp).symm.trans (congr_fun (summit v a x ht l q t) y)
    rw [show upT F hp y=i from up_downT F hp i w] at hw; refine hw.trans ?_; have hh: i=j ↔ y=x:= by
       have h1:upT F hp x=j:= up_downT F hp j le_rfl; have h2:upT F hp y=i:= up_downT F hp i w; exact ⟨fun H=> upT_faith F hp y x (h2.trans (H.trans h1.symm)), fun h=> h2.symm.trans ((congr_arg _ h).trans h1)⟩
    by_cases i=j; rw [if_pos ‹_›,hh.mp ‹_›,Pi.single_eq_same]
    rw [if_neg ‹_›,Pi.single_eq_of_ne (mt hh.mpr ‹_›)]
lemma cap_rank (q:m≤ l)(t:l≤ c)(i:(F.level h).Index)(w:wr (F.level h) i<r): (u'.ladder l i).2 0 r=0:=by
   let H:=F.level h; let d:= (H.bound i); let x:=downL F d i (le_refl (wt H i)); let v:=u'.supply _ d; let A:=u'.charm _ d
   exact (loft_upper v A x (lt_of_eq_of_lt (congr_arg Prod.snd (down_grade F d i (le_refl _))) w)).1 l q t
lemma step (q:m≤ l)(t:l<c)(i:(F.level h).Index): u'.ladder l i=pointStep A Ñ l N (wt (F.level h) i) k (u'.ladder (l+1) i):=by
    have hd:= (F.level h).bound i; have hv:=u'.charm _ hd; exact pier_step hv.simple hv.ratios t hv.cap ((u'.supply _ hd).mix _)
omit u'
lemma stationed (H:Hol G)(F:Frames G)(Q:Council F)(h k u p:ℕ) : ∃ W:Credit,∀ (P:TowerP F) (A:Levels G) (Ñ:ChartRatio G)(m c N)(X:ℝ), ∀ z:Stair Q P A Ñ m c N h p k u X,∀ l,m≤ l→l≤c→Palette (F.level h) (z.ladder l) k u p (W.buy X):=by
    let S i:=Enough (F.level i) p u k
    obtain ⟨W,v⟩:= uniformPays (P:=fun i X=>∀ y:ℝ,1≤y→(S i).buy y≤ Credit.buy X y) (Finset.Iic h) (fun i _=>⟨S i,fun _ _=>le_rfl⟩) (fun _ _ _ _ h p i y=> (p i y).trans (h i y)); refine ⟨W,fun P A Ñ m c N X z l a b=> ⟨z.funding H a b,fun i r w=>z.cap_rank a b i w,fun i e r p=>?_,fun r i j t=>z.principal H a b i j t⟩⟩
    let T:=F.level h; let d:=wt T i; have ht:d≤h:=T.bound i; let x:=downL F ht i (le_refl d); have H:= z.charm _ ht
    exact ((loft_allow (z.supply _ ht) H x).2 l a b e p r).more (v d (Finset.mem_Iic.mpr ht) X H.pos)
end Stair
variable {F':Frame G h}{Q':SectionData F'}
lemma climbs (p:Chartage Q' A Ñ m c N k u q X)(x:X≤Y):Chartage Q' A Ñ m c N k u q Y:= ⟨p.simple,p.ratios,p.order,p.length,p.cap,p.pos.trans x,p.age.trans x,p.ample,fun j i r v w a b=> (p.pays j i r v w a b).raise x⟩
end YM.WilsonCoeffUV.Mer.Xa
