import YM.RG05Readout.Harvest.Tends
/-!
# Composite report reading and reserve
Signed ONE-root evaluation therefore linear on all funded cluster moments and
 master vector inference.Photocard uses entire family request.Straps.WEM.A.
Also open to adding/raising power licences BEFORE limits.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Harvest
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Shadow Flatten Nuclear Halls Pulse
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {j b k ℓ t:ℕ}{e Q x E e' Q' Rg Rg' r a:ℝ}(h:C.Makes)
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "A!"=> C.S.a
local notation "Λ"=> C.S.toDepth
local notation "F₁"=> Site (C.side (n+1) p)
variable {D:Address.Rail C}{V:Type}[DecidableEq V][Fintype V]{P: Address.Sight C d p}{S: Address.Emblems C d} (hm: n+1 < m)(hv:b ≤ n)(hN:m ≤ N)
local notation "h₁"=>hm.le.trans hN
local notation "h₂"=> n.le_succ.trans hm.le
local notation "J"=> Bin G (C.side N p)
variable (ht:j ≤ b)
def chip (C:Family G)(p N n m d:ℕ)(h:n+1≤ N)(S : Emblems C d)(F:Bin G (C.side N p))(M:Palette C d) : Bin G (C.side N p):=
    F-crops C N p N d le_rfl (precinct C p N d (Many.point S M m N)) (n+1) h
local notation "X!p"=> chip C p N n m d h₁ S
structure Grip (C:Family G)(p N n m b d j:ℕ)(hm:n+1 < m)(hv:b ≤ n)(hN:m ≤N)(ht:j ≤ b)(S:Emblems C d)(F:Bin G (C.side N p))(M:Palette C d) (Q e Rg:ℝ): Prop where
   info : Sees C p N n m b d (Nat.le_trans n.le_succ hm.le) hv (hm.le.trans hN) S F M
   start : timely F
   silent': Silent d (chip C p N n m d (hm.le.trans hN) S F M)
   price: size M ≤ Q
   presence (z: Site (C.side b p))(he:separation z 0 ≤ (C.S.toDepth ht p).count.val/4) (f:Body)(hx:Cap (d+2) f 1):
        let X:=chip C p N n m d (hm.le.trans hN) S F M
        let y:= uniform C (n+1) p N d (hm.le.trans hN) X b z (1,false) f
        let T:= GridApprox.tilesAt C.S p ((ht.trans (hv.trans (Nat.le_succ n))).trans (hm.le.trans hN))
        Interior (T.chamber 0) y ∧ T.rootTest (C.beta N p) y ≤ e
   -- Uniform printer invoice at SAME physical b, in stated palette representation.
   paper : ∃ (P:Tape G (C.side b p)), pulseOut P = pulls C p N n d (hm.le.trans hN) F b hv ∧ ∃ Y, Printed C d (C.path.rep N p b) 0 (kappa C.path b) P Y ((finer S (hv.trans (n.le_succ.trans hm.le))).symm M) Rg
local notation "Ω"=>Grip C p N n m b d j hm hv hN ht S
variable (F:Bin G (C.side N p)){M:Palette C d} (hp: Grip C p N n m b d j hm hv hN ht S F M Q e Rg) {B:ℕ→ℕ→ℝ}(hw: Awake D B b d)
section
include hp
lemma Grip.grow {v u s:ℝ}(hu:Q ≤ v) (he:e ≤ u) (hS:Rg ≤ s) : Ω F M v u s:= {hp with presence:=fun z h f hx=> ⟨(hp.presence z h f hx).1,(hp.presence z h f hx).2.trans he⟩,price:= hp.price.trans hu,paper:=by obtain ⟨P,h,H,hr⟩:= hp.paper; exact ⟨P,h,H,hr.grow hS⟩}
include hw h
local notation "K"=> GridApprox.tilesAt C.S p ((ht.trans (hv.trans n.le_succ)).trans h₁)
local notation "Z"=> focus C E n b
lemma Grip.plus {W:Bin G (C.side N p)}{L:Palette C d}(hz: Ω W L Q' e' Rg'): Ω (F+W) (M+L) (Q+Q') (e+e') (Rg+Rg'):=by
    let T:= X!p F M; let V':= X!p W L; have he:X!p (F+W) (M+L)= T + V':=by
        unfold T V' chip; simp_rw [weave_fine hN, map_add, precinct_linear, crops_linear]; abel
    refine ⟨Sees.upward h _ _ _ hw hp.info hz.info hp.start hz.start,fun i=> Continuous.add (hp.start i) (hz.start i),?_, (size_add ..).trans (add_le_add hp.price hz.price),?_,?_⟩
    · rw [he]; exact fun i hi=> by rw [Pi.add_apply,show T i=0 from hp.silent' i hi,show V' i=0 from hz.silent' i hi,add_zero]
    rotate_left
    · obtain ⟨A,hA,y,hy⟩:=hp.paper; obtain ⟨V,hV,x,hx⟩:=hz.paper
      refine ⟨A+V,?_,y+x,?_⟩; rw [doubles h _ hv hp.start hz.start,←hA,←hV];rfl
      obtain ⟨s,b',α,β,P,Rx,K',-⟩:=(hw.toll p b N le_rfl (by omega)).author; let Z':=(K'.cursor.sense d le_rfl); rw [map_add]; exact hy.addP hx (h.wilson.represents _ _ _ (show b≤ N by omega)).good Z'.order Z'.power
    intro z h' f ht'; let a:= uniform C (n+1) p N d h₁ T b z (1,false) f; let b':=uniform C (n+1) p N d h₁ V' b z t! f; have hu: Interior ((K).chamber 0) a := (hp.presence _ h' f ht').1; have hα:Interior ((K).chamber 0) b':= (hz.presence _ h' f ht').1
    dsimp only;rw [he, uniform_add (he:=hv.trans n.le_succ)]; exact ⟨hu.plus hα, ((seamless h N p).semi (K) a b' hu hα).trans (add_le_add (hp.presence z h' f ht').2 (hz.presence z h' f ht').2)⟩ -- syntax
omit h
lemma Grip.scales (r:ℂ): Ω (r • F) (r • M) (‖r‖*Q) (‖r‖*e) (‖r‖*Rg):=by
    let T:= X!p F M; have he: X!p (r • F) (r • M)=r • T:=by unfold T chip; simp_rw [weave_fine hN,map_smul,precinct_scale,crops_scale,smul_sub]
    refine ⟨hp.info.times _ _ _ F hw r,fun i=> (hp.start i).const_smul r,?_,?_,?_,?_⟩
    · rw [he]; exact fun i hi=> by rw [Pi.smul_apply,show T i=0 from hp.silent' i hi,smul_zero]
    · rw [size_smul]; exact mul_le_mul_of_nonneg_left hp.price (norm_nonneg r)
    rotate_left
    · obtain ⟨A,hA,y,hy⟩:=hp.paper
      refine ⟨r • A,?_, r • y,?_⟩; rw [budgets, ← hA];rfl
      obtain ⟨s,b',α,β,P,L',K',-⟩:=(hw.toll p b N le_rfl (by omega)).author; let Z':=(K'.cursor.sense d le_rfl); rw [map_smul]; exact hy.twist Z'.order Z'.power r
    intro z hv' f hf; obtain ⟨hx,hy⟩:= hp.presence z hv' f hf; dsimp only; rw [he,uniform_s (he:=hv.trans n.le_succ),Next.Extract.root_smul]; exact ⟨hx.scale _,mul_le_mul_of_nonneg_left hy (norm_nonneg r)⟩
omit hp hw in
lemma Grip.free : Ω 0 0 0 0 0 :=by
   have he:X!p 0 0=0:=by unfold chip; simp_rw [weave_fine hN,map_zero,precinct_zero,crops_zero, sub_zero]
   refine ⟨Sees.zeroC ..,fun _=>continuous_const,?_, (size_zero.le),?_,?_⟩
   · rw [he]; exact fun _ _=> rfl
   rotate_left
   · refine ⟨0,?_,0,?_⟩; rw [vacC]; rfl; rw [map_zero]; exact Printed.blank (Real.sqrt_pos.mpr (forcedPos ..))
   intro z _ q _ ; let X_:Config G (C.side N p)→ℂ :=0; dsimp only; rw [he,uniform_zero (he:=hv.trans n.le_succ)]; refine ⟨Interior.constant (G:=G) _ 0,?_⟩; refine le_of_eq ?_; have h:=Next.Extract.root_smul (K) (C.beta N p) X_ 0; simp only [X_,smul_zero,norm_zero,zero_mul] at h; exact h
end
section attain
variable {ψ:ℕ→ℕ}{w:Worth}(Yc:OPE.Package C w ψ D)(hC:Storage C D)(hS:Cater C D) (s:V→ℕ)(u: V→ Cover)(f:V→Body)
    (H: Knock b n m p k d ℓ t r a C s u f)(x:(i:V)→Palette C (s i))
local notation "g"=> fun j:V=>Lattice.wrap (C.side (n+1) p) (u j)
variable (A:(i:V)→Sight C (s i) p)(U:(i:V)→ Emblems C (s i))(fW:PulseC)
    (hW: Priced d fW 1)(hp₁:∀ i:V,size (x i)≤ Q)(hQ:0 < Q)
variable (h'A :∀ i:V,Spine D B h (n+1) p (s i) N (A i) (U i))
    (hU:Spine D B h b p d N P S)(hg:d+3 ≤ C.path.levels.clock.J n)
local notation "X"=> bunchG (C:=C) (N:=N) g s f (fun i:V=> Many.point (U i) (x i) m N)
local notation "W"=> fun φ:Body=> (fW φ) • X
local notation "F!"=> Fintype.card (Color V)
local notation "a!"=> tender C m n d ℓ k (F!) Q
local notation "e!"=> copperE C m n d ℓ k (F!) Q
local notation "q!"=> copperH C m n d ℓ k (F!) Q
noncomputable def thresholdC (C:Family G)(e:ℝ)(j b n d:ℕ):= Real.exp (baseT C j b d)/focus C e n b
-- independent of cutoff and period; payable (and monitor hypothesis uses same hN)
def printing (C:Family G)(b n m d ℓ k t:ℕ) (hv:b ≤ m) (Q B:ℝ) :ℝ := max 0 (Shadow.tab C (Shadow.bid C n d (copperE C m n d ℓ k t Q)) n b + B * (advanceCost C d hv * tender C m n d ℓ k t Q))
include h hW hp₁ hQ h'A hU hw hg Yc hC hS H
lemma spawned (hX:16*(1+t+Scope C ℓ) ≤ (C.S.toDepth ht p).count.val)(h_Open:Stock.Tabs.opens C.path.levels (bumper (2*t)) j b)(hPin: ∀ i,b≤ i→Pin C i d) : ∃ T:Palette C d, Grip C p N n m b d j hm hv hN ht S W T (a!) (thresholdC C q! j b n d) (printing C b n m d ℓ k (F!) (hv.trans (h₂)) Q (B d b)):=by
    let q':= copperH C m n d ℓ k (F!) Q
    obtain ⟨R,T,hR⟩:=originates h Yc hC hS s u f H x A U P S fW hW Q hp₁ hQ h'A hU hw hg hN; let v:= finer S h₂ (R n-advances S R b n); let V!:= W; have hΨ: pulls C p N n d h₁ V! n (le_refl n)=amplitude C n N p d fW (dyes C (n+1) N p h₁ X) :=by rw [wakes, show arises C p N n h₁ V! =_ from (show arises C p N n h₁ V! = fun φ=> fW φ • dyes C (n+1) N p h₁ X from funext (fun _=> dye_pitch _ _ _))]
    obtain ⟨hp,hE⟩:=onAll h Yc hC hS s u f H x A U P S fW hW hp₁ hQ h'A hU hw hg hN hR hPin j ht h_Open; let z:= Many.point S v m N
    exact ⟨v,⟨reports h h₂ hv h₁ V! hw hU T R e! (hΨ.symm ▸ hR),fun i=> Continuous.const_smul (show Continuous (X) from continuous_finsetProd _ (fun j _=> clinic_cut ..)) (fW i),quiet fW hW h₁ z X, hp,fun y h₀ f' hx=> ⟨plotIn h ht (hv.trans n.le_succ) h₁ y h₀ hX _ _ _ _ fW z f' H.grade H.rank H.near, (hE y h₀ f' hx).2⟩, by
          obtain ⟨P,hP,Y,hYP⟩:= reports_tt h h₂ hv h₁ V! hw hU T R e! (hΨ.symm ▸ hR); let l:= hv.trans h₂
          have hb:0≤B d b:= zero_le_one.trans ( (hU.legal b le_rfl (l.trans hN)).pos)
          let u:=advanceCost C d l; have hs:size ((finer S l).symm v)≤u*a! :=(Spine.downsized h hU (le_refl b) l hN v).trans (mul_le_mul_of_nonneg_left hp (advanceCost_pos _|>.le))
          exact ⟨P,hP,Y,hYP.grow (le_trans (add_le_add_right (mul_le_mul_of_nonneg_left hs hb) _) (le_max_right ..))⟩⟩⟩
end attain
end YM.RG05Readout.Harvest
