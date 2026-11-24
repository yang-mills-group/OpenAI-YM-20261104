import YM.FormalBulk08.Spruce.Bloom
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spruce
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis Castor
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{X:Type}{E m n l e r j t d D R:ℕ}{F:Frame G d}{T:SectionData F}{W:Lab G K X}{H:Hol G}
variable {ρ:ChartRatio G}{o:Loc G 1}{Y Z:X→Anthem D G}{g:X→ℝ}{θ:ℝ}
lemma tenderJoin {T S:X→Studio D→Tile (edgeL G) r} {τ : Time X}{η δ:X→ℝ}(hp:Tender τ o η g T)(hw:Tender τ o η g S)(h:Tender τ o η (fun i=>δ i*g i) (fun i p=>T i p-S i p)) : Brass τ o η δ g T S:= by refine ⟨hp,hw,?_⟩; unfold Tender at h;simp_rw [mul_assoc] at h; exact h
lemma brass_fold_gen {I:Type} {T S:X→ Studio D→ Tile (edgeL G) r}{δ η:X→ℝ} (u:I→X){τ:Time X}{t:Time I}(hp:Soft t (fun i=>τ.day (u i)))(h:Brass τ o η δ g T S): Brass t o (fun i=>η (u i)) (fun i=>δ (u i)) (fun i=>g (u i)) (fun i=>T (u i)) (fun i=> S (u i)):= tenderJoin (tenderLift (p:=u) hp (show Tender τ o _ g _ from h.1)) (tenderLift (p:=u) hp (show Tender τ o _ g _ from h.2)) (tenderLift (p:=u) hp (brass_crisp h))

variable (q:Quota F H W o D E R)(u:Use W ρ E)(h:LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)(C P Q:Pin W.scrolls)(hp:∀ i,C.N i≤ P.N i)(hz:∀ i,P.N i≤Q.N i)(hl:l≤R)(hR:d≤ R)
   (hg:∀ i,0≤ g i)(hy:∀ i,Clef o (Y i) l)(hx:∀ i,Clef o (Z i) l)
   (hw:∀ e≤ E,∀ r,Brass ((sage C).reach (peak C)) o (fun i=> W.eagle (peak C i)) (hill C P hp) g (fun x p=> Y x p e r) (fun x p=> Z x p e r))
include q u hw hR hy hx
lemma ankle (i:Letter F) (j:ℕ)(he:j≤ E) : Faint ((sage C).reach (peak C)) (fun i=>hill C P hp i*g i) (fun x=>coeff j (echo F (Y x) i)-coeff j (echo F (Z x) i)):= by
    have ht := pricer (D:=D) q u C (Y:=fun i=>Y i-Z i) (fun j hj r=> brass_crisp (hw j hj r)) hR i j he; exact ht.lower (fun p=> by rw [Clover.chalk_less F i (hx p).fare (hy p).fare,map_sub])
include hz hp hg h a hs ht hb hl
lemma wintry (p:θ<1/2)(h':θ≤ 1):∀ e≤ E,∀ r,Brass (sage C) o W.eagle (fun i=>hill C P hp i.a) (fun i=> g i.a* Degree θ i) (fun i t=> wave (T:=T) l ρ q a C P i Y t e r) (fun i t=>wave (T:=T) l ρ q a C Q i Z t e r):= by
   let X'(i:Deck C):= wave (T:=T) l ρ q a C P i Y; let P'(i:Deck C):=wave (T:=T) l ρ q a C Q i Z; let T' x:= tribal (T:=T) (ρ:=ρ) q a P.N (x:Deck C);let Y' x:=tribal (T:=T) (ρ:=ρ) q a Q.N (x:Deck C)
   let Z1:=hill C P hp; let b(x:X):=Z1 x*g x; have hb' x: 0≤b x:=mul_nonneg (limb_pos ..) (hg _)
   have hl' i := (hp i).trans (hz i)
   have H1 i j (hj:j ≤ E)(r:ℕ): Brass (sage C) o W.eagle (fun i=>Z1 i.a) (fun _=>1) (fun x p=> T' x i p j r) (fun x p=>Y' x i p j r):= brass_fold (Lab.raiseD C P hp) (soft_day _) (Elm.truss q u P Q hz h hs ht hb a hR i hj r) (fun i=> bend_up C P hp i targetPower_pos.le)
   have hT x: Court o F (T' x):= birth a h q hs ht hb _ _ _ x.zone (x.cap.trans (hp _)); have hz' x:Court o F (Y' x):= birth a h q hs ht hb _ _ _ x.zone (x.cap.trans (hl' _))
   have Ho e (he:e≤E) r:= (hw _ he r).1;have Hq e (he:e≤ E) r:= (hw _ he r).2; obtain Hv:= timbre q u h a hs ht hb C P hp hl hg hy Ho hR p h'; obtain H:= timbre q u h a hs ht hb C Q hl' hl hg hx Hq hR p h'
   have Hu:=confidential q u h a hs ht hb C P hp hy (tender_qual hg Ho);have hz:=confidential q u h a hs ht hb C Q hl' hx (tender_qual hg Hq)
   let t:= fun i:Deck C=>g i.a*Degree θ i
   let A e r:= Brass (sage C) o W.eagle (fun i=>Z1 i.a) t (fun i p=>X' i p e r) (fun i p=>P' i p e r); have hv i r (hi:l+i<r):A i r:=by
       unfold A; simp_rw [show ∀ x p,X' x p i r=0 from fun x p=> Classical.byContradiction fun h=> (not_lt_of_ge ((Hu x).1.fare.1 _ _ _ h)) hi,show ∀ x p,P' x p i r=0 from fun x p=>Classical.byContradiction fun h=>(not_lt_of_ge ((hz x).1.fare.1 _ _ _ h)) hi]; exact mates_void ..
   suffices ∀ i j, i≤E → j≤ l+i→ A i j from fun i hi r=> by by_cases hx:r≤l+i; exact this i r hi hx; exact hv i r (lt_of_not_ge hx)
   apply goyal; intro e r hE hl' ih; have hA j m (hp: precede e r j m): A j m:= by by_cases hh:m≤ l+j; exact ih j m hp hh; exact hv j m (lt_of_not_ge hh)
   let T1 (i:Deck C) (p):= X' i p e r-P' i p e r; have hk: Tender (sage C) o W.eagle (fun i=> b i.a *Degree θ i) T1 := by
       apply tanne u.liable p h' hb'
       · have ht: Nextpay o (Dove.tide C) _ _ _ _ _ _ _ := (capsule (e:=e) (r:=r) (T:=fun i=>X' (Turn.ups i)) (S:=fun i=> P' (Turn.ups i)) (budge C P Q hp ‹∀ i,P.N i≤Q.N i› u h a hs) (payroll_from C q u P.N) (hδ:=fun i=>show 0≤ t i.ups from mul_nonneg (hg _) (ratioR_pos ..).le) (fun i=>hT i.bed) (fun i=> hz' i.bed) (fun i=> (Hu i.ups).1) (fun i=> (hz i.ups).1) (fun i=> (Hu i.ups).2.2) (fun i=>(hz i.ups).2.2) (fun i=> (Hu i.ups).2.1) (fun i=> (hz i.ups).2.1) (by omega) hE hR hl (scooped C) (fun j m hp=> brass_fold_gen (Turn.ups (C:=C)) (up_age C u.liable) (g:=t) (hA j m hp)) (tenderLift (p:=Turn.ups) (up_age C u.liable) (H _ hE r)) (fun y j hx=> brass_fold (p:=Turn.bed) (down_age C) (H1 y j (hx.trans hE) r) (fun _=>le_refl _))).1
         change Nextpay _ _ _ _ _ (fun i=>Z1 i.a*g i.a*Dove.bump θ i) _ (fun i=>T1 i.ups) (fun i p=> X' i.bed p e r-P' i.bed p e r); simp_rw [show ∀ i:Turn C,X' i.bed=_ from fun i=>waved _ ρ q a C P i, show ∀ i:Turn C,P' i.bed=_ from fun i=>waved _ ρ q a C Q i,mul_assoc]; exact ht
       unfold T1; simp_rw [show ∀ x,X' (peak C x)=_ from fun x=> wave_last (T:=T) l ρ q a C P x,show ∀ x,P' (peak C x)=_ from fun x=>wave_last (T:=T) l ρ q a C Q x]
       have he (i:X)(p:Studio D): canopy F (T' (Dove.peak C i)) (Y i) p e r-canopy F (Y' (Dove.peak C i)) (Z i) p e r=Y i p e r-Z i p e r-(crease F (T' (peak C i)) (Y i) p e r- crease F (Y' (peak C i)) (Z i) p e r):= by unfold canopy; simp only [Pi.sub_apply];abel
       change Tender _ _ _ _ (fun i p=> canopy F (T' _) _ _ _ _-canopy F (Y' _) _ _ _ _); simp_rw [he]; refine Bear.minus (brass_crisp (hw e hE r)) (matchScale e r (fun i=>hT (peak C i)) (fun i=> hz' (peak C i)) (fun i j hj=> brass_fold (peak C) (soft_day _) (H1 i j (hj.trans hE) r) (fun _=>le_rfl)) (fun j k hj=>?_)); have ht : j≤E:= by omega
       exact ⟨pricer q u C Ho hR k j ht, ankle q u C P hp hR hy hx hw k j ht⟩
   refine tenderJoin (T:=fun i p=>X' i p e r) (S:=fun i p=>P' i p e r) (Hv _ hE r) (H _ hE r) ?_; convert hk using 1; ext x; exact (mul_assoc ..).symm
end YM.FormalBulk08.Spruce
