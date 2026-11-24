import YM.RG20.Eye
import YM.UVExtension.Rainfall.Ascot
/-!
# Transport an extra native reserve through the complete single-source step
Source adapted from UVExtension/Lacing/{Wallet,Merge}.lean, UVExtension/Rainfall/Jet.lean. Re-specialize and re-check against
the UV Rama (Rainfall/Lacing) data; no identification of independent witnesses. See ledger.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lacing
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open Eyelet MergeProof
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p m : ℕ) (A : Hol G)
open Extra.Histories.InputColumn
local notation "κ"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
local notation "Λ"=> Real.sqrt (H.levels.clock.forcedAllowance m)
variable {T : Extra.Histories.Heading F} {C η t w : ℝ}
local notation "n"=> H.S.side m p
local notation "n'"=> H.S.side (m+1) p
local notation "Old"=> H.rep N p (m+1)
set_option quotPrecheck false
local notation "R"=> H.rep N p m
local notation "O" => Bucket F (R).p A n
set_option quotPrecheck false
structure Sends20 (D:GaugeDoor Old R) (X:Set Wing) (α : Config G n'→ℂ)(ρ:Res G n') (ψ:ℂ) (g:Config G n'→ℂ) (v:F.Coeff) (c t w:ℝ)(q:Bucket F (R).p A n) : Prop where
    mints: ∃ P:Coefficient F n, Gig B H N p m A g P v c t ∧ Tale X 0 0 (((H.S.block m).val:ℂ)^d) α ρ (profile (R).activities P.forced) ψ w t D ∧ Blown P 0 R (t/turnCost (R).p.order (R).p.power) ∧ Eye P A R Λ=q
variable (Z : Keeper (H.rep N p (m+1)).p (H.rep N p (m+1)).activities)
    (D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m)) (X:Set Wing)
lemma rents20 (q:(O)) {α : Config G n'→ℂ}{ρ:Res G n'}{ψ:ℂ}{g:Config G n'→ℂ} {v:F.Coeff}{c t w p0 u y:ℝ}(h:Sends20 B H N p m A D X α ρ ψ g v c t w q)(hc:c≤p0)(hu:t≤ u)(hw:w≤ y): Sends20 B H N p m A D X α ρ ψ g v p0 u y q:=by
    obtain ⟨P,h,hS,hB,hZ⟩:= h.mints; exact ⟨P,h.weaken hc hu,hS.climb le_rfl hw hu,hB.enlarge (by gcongr; unfold turnCost; positivity),hZ⟩


variable (L:RoutesF F (H.S.side m p) (H.S.side (m+1) p) (H.rep N p (m+1)).p (H.rep N p m).p A)
structure Manor20 (V :Heading F)(C η t:ℝ) : Prop where
    coins : Nonempty (Keeper (R).p (R).activities)
    route : L.route= cart («R»:=Old) Z
    good : SoundDoor (H.levels.clock.op m p) D
    map_norm x: F.coeffSize (V.map x) ≤ C*F.coeffSize x ∧ F.coeffSize (V.map.symm x)≤ C*F.coeffSize x
    pivot i: let v:=seed F i; let P:=Extra.Histories.primary (0:Site n') v
             Sends20 B H N p m A D X (P.exponentialEntry 0 B Old) 0 (v 0) (P.density 0 B Old) (V.leads (H.S.block m) v) (η*F.coeffSize (F.core v)) (C*F.coeffSize (vowel F (H.S.block m) (F.core v))) (peat t (F:=F) i) (L.vane i)
    glass (i:Eyelet.Slot n') (j:Birth A i.1 (Old).p d) c: let u:= (Old).p.mass i.1.val c
              (Old).p.supBounds 0 i.1.val j.val c → Sends20 B H N p m A D X (masked (Old).p.threshold i.1.val j.val) 0 0 (salary Old i.1.val j.val) 0 (η*u) (η*u) (2*u) (L.glass i ((fee (Old).p i.1.val:ℂ) • twig (tin d A i.1 (Old).p) j))
    wing i (x:Eyelet.Bolt (G:=G) (Old).p i) a : let j:= L.route i; let u:=(Old).p.mass i.val.1 a
               0 ≤ a → (∀ U, ‖x.val U‖ ≤ a) → Sends20 B H N p m A D X 0 (exactGas (Old).activities j x.val) 0 (Extra.Histories.fare Old j x.val) 0 (η*(u/κ)) (η*(u/κ)) (2*u) (L.wing i ((((fee (Old).p i.val.1 / κ):ℝ):ℂ) • twig (sink (G:=G) (Old).p i) x))

local notation "t'"=> Doors.rate (H.S.block m)
lemma leisure20 (q:GaugeDoor Old R)  {t u:ℝ}(ht:0≤ t)(hu:0≤u) : Sends20 B H N p m A q X 0 0 0 0 0 t t u 0:=by
   -- Need Keeper for Eligible to see projection.Eye=0 even if not.
   let P:Coefficient F n:= Extra.Histories.primary 0 0; have hp: P.Format 0 A R:= primary_format _
   have he: P.density 0 B R=0:=by
      funext V; rw [show P.density 0 B R V= _ from primary_density B (R) 0 V];change _*part B 0 R V 0=0;rw [map_zero,mul_zero]
   have hκ: P.remBound 0 R (kappa H m) 0:= primary_rem _ (Real.sqrt_pos.mpr (forcedPos _ _))
   obtain ⟨a,b,hb,h₁⟩:= rem_tabs.mp hκ
   have h2:a=0∧ b=0:= by have hz:=hb.first; have hr:=hb.second; constructor<;>linarith
   obtain ⟨rfl,rfl⟩:=h2
   refine ⟨P,⟨hp,?_,by simpa only [P, Extra.Histories.primary,sub_zero,Frame.coeffSize,Pi.zero_apply,norm_zero,sum_const_zero,mul_zero] using ht, 0,0,hb,by rw [mul_zero,add_zero]; exact ht⟩,?_,Blown.primary _ (by unfold turnCost; positivity),?_⟩
   · have hx:= (H.levels.transition_mass m p (Old).beta); rw [he,Extra.Histories.blast]; funext x; simp [StepData.push]
   · rw [show profile (R).activities P.forced = 0 by funext i j; simp [profile,P,cram,Extra.Histories.primary]]; exact taped hu ht
   unfold Eye; split; next h=> exact Prod.ext rfl (Prod.ext (Eligible.blankC h|>.1) (Eligible.blankC h|>.2))
   next =>rfl
end YM.UVExtension.Lacing


set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lacing
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open Eyelet MergeProof
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p m : ℕ) (A : Hol G)
open Extra.Histories.InputColumn
local notation "κ"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
local notation "Λ"=> Real.sqrt (H.levels.clock.forcedAllowance m)
variable {T : Extra.Histories.Heading F} {C η t w : ℝ}
local notation "n"=> H.S.side m p
local notation "n'"=> H.S.side (m+1) p
local notation "Old"=> H.rep N p (m+1)
set_option quotPrecheck false
local notation "R"=> H.rep N p m
local notation "O" => Bucket F (R).p A n
set_option quotPrecheck false
section
variable {ι:Type}[Nonempty ι][Countable ι]
  {f : ι → Config G (H.S.side (m+1) p)→ℂ}
  {v : ι→ F.Coeff}{u a z:ι→ℝ}
set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 400000 in
lemma vouchers20 {X:Set Wing} (q:GaugeDoor Old R)(hq: SoundDoor (H.levels.clock.op m p) q)
    (h:Vintage.YM.RG.History.Selected H)(hm:m≤N)(hCoins: Nonempty (Keeper (R).p (R).activities)) {g:ι→ Config G n'→ℂ}{w':ι→ Res G n'}{t:ι→ℂ}{φ:Config G n'→ℂ}{ψ:Res G n'}{σ:ℂ}(y:ι→Bucket F (R).p A n)(hp:∀ j,Sends20 B H N p m A q X (g j) (w' j) (t j) (f j) (v j) (u j) (a j) (z j) (y j))(hg:∀ U,HasSum (fun i=>g i U) (φ U))(hx:∀ i U,HasSum (fun j=> w' j i U) (ψ i U))(ht:HasSum t σ)
    (hf:Dominated f)(hk:∀i,Measurable (f i)) (hv:Summable fun i=> F.coeffSize (v i))(hu:Summable u)(ha:Summable a)(hζ:Summable z):
    Sends20 B H N p m A q X φ ψ σ (fun V=> ∑' i,f i V) (∑' i,v i) (∑' i,u i) (∑' i,a i) (∑' i,z i) (∑' j,rooms n F A (R).p (aisleN (code ι) j) (y j)):=by
   choose Q hQ Hq hBq hδ using fun j=> (hp j).mints
   let P:= Extra.Histories.merge (code ι) Q
   have hκ:0<Λ:= Real.sqrt_pos.2 (forcedPos ..)
   have hA':= Vintage.YM.MergeProof.Gig.all_in B H N p m A h hm hQ hf hk hv hu ha
   refine ⟨P,hA', Tale.upon hq Hq hg hx (fun i U=> profile_merge (code _) Q hκ (fun i=> (hQ i).bound) ha i U) ht ⟨fun i=>?_,hζ,le_rfl⟩ ⟨fun i=> rem_nonneg ((hQ i).bound),ha,le_rfl⟩,?_ ,?_⟩
   · obtain ⟨ι,h,P,p,ψ,H⟩:= Hq _; exact sumBudget_credit H.purchase
   · let X:= turnCost (R).p.order (R).p.power
     have hb : Blown P 0 R (∑' i, a i / X) := Blown.joins _ hBq (ha.div_const X)
     rwa [tsum_div_const] at hb
   have hj(i):Eligible (Q i) A (R) Λ:=⟨hCoins,(hQ i).format,_,(hQ i).bound⟩
   have hz':Eligible P A (R) Λ:=⟨hCoins,hA'.format,_,hA'.bound⟩
   have heZ(i):  F.coeffSize (Q i).x ≤ u i + F.coeffSize (v i):= by
      let z:= v i; let y':=(Q i).x-z
      have he' := Work.G08.size_triangle F (Q i).x z
      have hy := (hQ i).leadP; linarith only [le_mul_of_one_le_left (Work.G08.size_nonneg F y') (orbitCost_one_le F),he',hy]
   have hh:= stanza (code _) Q (fun i=> (hQ i).bound) ha hj hz' ((hu.add hv).of_nonneg_of_le (fun _=> Work.G08.size_nonneg ..) heZ)
   simp_rw [hδ] at hh; exact hh.tsum_eq.symm
end
end YM.UVExtension.Lacing

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Rainfall
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open Eyelet MergeProof Lacing
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p m : ℕ) (A : Hol G)
open Extra.Histories.InputColumn
local notation "κ"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
local notation "Λ"=> Real.sqrt (H.levels.clock.forcedAllowance m)
variable {T : Extra.Histories.Heading F} {C η t w : ℝ}
local notation "n"=> H.S.side m p
local notation "n'"=> H.S.side (m+1) p
local notation "Old"=> H.rep N p (m+1)
local notation "Out"=> H.rep N p m
local notation "F1"=> F.Coeff
set_option quotPrecheck false
structure Flees20 (E:Rep G n')(R:Rep G n)(D:GaugeDoor E R) (X:Set Wing) (α : Config G n'→ℂ)(ρ:Res G n') (ψ:ℂ) (g:Config G n'→ℂ) (v:F.Coeff) (c t w:ℝ)(q:Bucket F R.p A n) : Prop where
    mints: ∃ P:Coefficient F n, Gig B H N p m A g P v c t ∧ Tale X 0 0 (((H.S.block m).val:ℂ)^d) α ρ (profile R.activities P.forced) ψ w t D ∧ Blown P 0 R (t/turnCost R.p.order R.p.power) ∧ Eye P A R Λ=q
variable (E:Rep G (H.S.side (m+1) p)) (R:Rep G (H.S.side m p))(D:GaugeDoor E R)(X:Set Wing)
    (K:Keeper E.p E.activities)(L:RoutesF F (H.S.side m p) (H.S.side (m+1) p) E.p R.p A)
open MergeProof
structure Palace20 (r:Side)(V :Heading F)(C η t:ℝ): Prop where
    coins : Nonempty (Keeper R.p R.activities)
    route : L.route= cart (R:=E) K
    good : SoundDoor (H.levels.clock.op m p) D
    map_norm x: F.coeffSize (V.map x) ≤ C*F.coeffSize x ∧ F.coeffSize (V.map.symm x)≤ C*F.coeffSize x
    pivot i: let v:=seed F i; let P:=Extra.Histories.primary (0:Site n') v
             Flees20 B H N p m A E R D X (P.exponentialEntry 0 B E) 0 (v 0) (P.density 0 B E) (V.leads r v) (η*F.coeffSize (F.core v)) (C*F.coeffSize (vowel F r (F.core v))) (peat t (F:=F) i) (L.vane i)
    glass (i:Eyelet.Slot n') (j:Birth A i.1 E.p d) (c:ℝ): let u:= E.p.mass i.1.val c
              E.p.supBounds 0 i.1.val j.val c → Flees20 B H N p m A E R D X (masked E.p.threshold i.1.val j.val) 0 0 (salary E i.1.val j.val) 0 (η*u) (η*u) (2*u) (L.glass i ((Eyelet.fee E.p i.1.val:ℂ) • twig (tin d A i.1 E.p) j))
    wing  (i:StockTag (H.S.side (m+1) p)) (x:Eyelet.Bolt (G:=G) E.p i) (a:ℝ) : let j:= L.route i; let u:=E.p.mass i.val.1 a
               0 ≤ a → (∀ U, ‖x.val U‖ ≤ a) → Flees20 B H N p m A E R D X 0 (exactGas E.activities j x.val) 0 (Extra.Histories.fare E j x.val) 0 (η*(u/κ)) (η*(u/κ)) (2*u) (L.wing i ((((Eyelet.fee E.p i.val.1 / κ):ℝ):ℂ) • twig (sink (G:=G) E.p i) x))
variable (hr: H.rep N p m= R)(he: H.rep N p (m+1)=E)
lemma seat20 (V' : RoutesF F n n' (Old).p (Out).p A)(t:ℝ){r:Side}(h:H.S.block m=r)(hp: Palace20 B H N p m A E R D X K L r T C η t)(hzL:HEq V' L) : Manor20 B H N p m A (shim H N p m E K he) (duet H N p m hr he D) X V' T C η t:=by
    subst E R r; obtain rfl:= eq_of_heq hzL; exact ⟨hp.coins, hp.route,hp.good,hp.map_norm,fun i=> ⟨(hp.pivot i).mints⟩,fun i j c hu=> ⟨(hp.glass i j c hu).mints⟩,fun i x a hV hU=> ⟨(hp.wing i x a hV hU).mints⟩⟩
include hr

lemma blows_of_fancy {X' : ℕ→ Support n}{M:Push.Local.Raw F n}{w t u:ℝ}{f:Config G n'→ℂ}{v:F.Coeff}
    (hx:H.Conv N p m)(hR:Readable A B R.p n w) (h:Fancy B H N p m A f X' M v w t u)(K':Keeper R.p R.activities):
    Blown (wallet K' X' B M A) 0 R (u/turnCost R.p.order R.p.power):=by
   subst R
   obtain ⟨a,b,c,⟨h₁,-⟩,_,hv,⟨pQ,q,hq,h₃⟩,hA,_⟩:=h
   let S := K'.supply (fun i=> joint B (0:Site n) (X' i))
   let T₀ := (Out).p
   have hB : Blown (wallet K' X' B M A) 0 Out a := h₃ ▸ Blown.deck S h₁ hR hq
   apply hB.enlarge
   have hκ:0<kappa H m:= Real.sqrt_pos.mpr (forcedPos ..)
   have hb : 0 ≤ b+c := (tab_mint S h₁ hx.good hκ hR hv).second
   rw [le_div_iff₀ (by exact lt_of_lt_of_le zero_lt_one (Lacing.RoutesF.turnCost_near _))]
   linarith only [hA, hb]

include he hr
lemma breeze20 {u t:ℝ}(ht:0≤ t)(hu:0≤u): Flees20 B H N p m A E R D X 0 0 0 0 0 t t u 0:=by subst E R; exact ⟨(leisure20 B H N p m A X _ ht hu).mints⟩
lemma dormant20 {C η t:ℝ} (T:Heading F) (r:Side) :
    let v:=seed F none; let P:=Extra.Histories.primary (0:Site n') v
    Flees20 B H N p m A E R D X (P.exponentialEntry 0 B E) 0 (v 0) (P.density 0 B E) (T.leads r v) (η*F.coeffSize (F.core v)) (C*F.coeffSize (vowel F r (F.core v))) (peat t (F:=F) none) 0:=by
   intro v P; have hv:v=0:=rfl
   have hJ:P.exponentialEntry 0 B E=0:=by
      funext U; change part B 0 E U (0:F.Coeff)+∑' i,P.maskedTerm E i U=0; rw [map_zero,zero_add]; simp_rw [show ∀ i,P.maskedTerm E i U=0 from fun i=> congr_fun (map_zero (Push.Local.maskLinear _ _)) _,tsum_zero]
   rw [hJ, show P.density 0 B E=0 from funext fun U=> by unfold P; rw [primary_density,hv,map_zero,mul_zero]; rfl, hv,Pi.zero_apply,map_zero (T.leads r),map_zero]; rw [show vowel F r 0=0 from funext fun i=>by simp [vowel], show F.coeffSize 0=0 from by simp [Frame.coeffSize],mul_zero,mul_zero]; exact breeze20 B H N p m A E R D X hr he le_rfl (by exact le_rfl)
lemma shrine20 (T:Heading F)(C w t:ℝ)(r:Side)(hz:H.S.block m=r)(hm:m<N)(hp:Vintage.YM.RG.History.Selected H)(hK : Keeper R.p R.activities)(hc:0≤ t): let v:= seed F (some 0); let P:= Extra.Histories.primary (0:Site n') v
    Flees20 B H N p m A E R D X (P.exponentialEntry 0 B E) 0 (v 0) (P.density 0 B E) (T.leads r v) (w*F.coeffSize (F.core v)) (C*F.coeffSize (vowel F r (F.core v))) t ((((r.val:ℂ)^d) • v),0):=by
   subst R E r; intro v P
   change Flees20 B H N p m A _ _ _ X _ _ (F.e0 0) _ (T.leads _ F.e0) (w*F.coeffSize (F.core F.e0)) (C*F.coeffSize (vowel F _ (F.core F.e0))) t _
   let L:= H.S.block m; let x:ℂ:= (L.val:ℂ)^d
   have hx : T.leads L F.e0=x • F.e0 := by
    change T.map (vowel F L F.e0) = _
    rw [show vowel F L F.e0 = x • F.e0 by
      funext i
      by_cases hi : i=0
      · rw [hi]; simp [x,vowel,F.zero_degree]
      simp [vowel,Frame.e0,Pi.single_eq_of_ne hi],map_smul,T.unit]
   rw [Size.unit_core, show vowel F L 0=0 from funext fun i=>by simp [vowel], show F.coeffSize 0=0 from by simp [Frame.coeffSize],mul_zero,mul_zero]
   let R:= Extra.Histories.primary (0:Site n) (x • F.e0)
   have hu:P.exponentialEntry 0 B Old= fun _=>1:=by
      funext U
      have he j:P.maskedTerm Old j U=0:= congr_fun (map_zero (Push.Local.maskLinear _ _)) U
      change F.e0 0+maskLinear _ _ (presented B 0 _ (F.core F.e0)) U+∑' j,P.maskedTerm Old j U=1; rw [Size.unit_core]; simp only [map_zero,Pi.zero_apply,add_zero,Frame.e0,Pi.single_eq_same,he,tsum_zero]
   have hκ:R.remBound 0 Out (kappa H m) 0:= primary_rem _ (Real.sqrt_pos.mpr (forcedPos _ _)); have hw:=hκ; obtain ⟨a,b,hb,hA⟩:= rem_tabs.mp hw
   have ha:a=0∧b=0:=by have h:=hb.first; have h':=hb.second; constructor<;> linarith
   obtain ⟨rfl,rfl⟩:= ha
   have hE:Eligible R A Out (kappa H m):=⟨⟨hK⟩,primary_format _,_,hκ⟩
   refine ⟨R, ⟨primary_format _,?_ ,?_, 0,0,hb,by simp⟩,?_,by unfold R; exact Blown.primary _ (by rw [zero_div]),?_⟩
   · have hz : blast H N p m d (P.density 0 B Old)=x • liftVac H N p m:=by unfold P;rw [show v=F.e0 from rfl,unit_density]; exact Vintage.YM.Extra.Histories.blast_vac H N p m d hp hm
     unfold R; rw [hz,show Extra.Histories.primary (0:Site n) (x • F.e0) = Extra.Histories.stretch x (Extra.Histories.primary 0 F.e0) by simp [Extra.Histories.stretch,Extra.Histories.primary]]
     funext V; rw [stretch_density,_root_.YM.Extra.Histories.unit_density];rfl
   · rw [hx]; simp [R,Extra.Histories.primary,Frame.coeffSize]
   · rw [hu, show profile (Out).activities R.forced=0 by funext i j; simp [R,Extra.Histories.primary,profile,cram],Frame.e0,Pi.single_eq_same]; exact taped hc le_rfl
   rw [hE.vistas]; exact Prod.ext rfl (Prod.ext (Eligible.blankC hE|>.1) (Eligible.blankC hE|>.2))

end YM.UVExtension.Rainfall
